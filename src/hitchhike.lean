import control.monad.basic
import linear_algebra.matrix
import algebra.group

universes u v

open function

class has_extract (m : Type u → Type u) :=
  (extract : Π {α}, m α → α)

class has_extend (m : Type u → Type u) :=
  (extend : Π {α β}, (m α → β) → m α → m β)

class has_duplicate (m : Type u → Type u) :=
  (duplicate : Π {α}, m α → m (m α))

export has_extend (extend)

infixl ` =>> `:55 := flip extend

class comonad (m : Type u → Type u) extends functor m, has_extract m, has_extend m, has_duplicate m : Type (u+1) := (duplicate := λ α (ma : m α), ma =>> id)

class is_lawful_comonad m extends comonad m, is_lawful_functor m := 
  (extend_extract : ∀ {α}, extend extract = (id : m α → m α))
  (extract_extend : ∀ {α β} {f : m α → β}, extract ∘ extend f = f)
  (extend_extend : ∀ {α β γ} {f : m α → β} {g : m β → γ}, extend g ∘ extend f = extend (g ∘ extend f) )

def store (α β : Type) := α → β

instance (ix) [add_monoid ix] : functor (store ix) :=
  {
    map := λ α β f ma, f ∘ ma,
    map_const := λ α β b ma, const ix b,
  }

instance (ix) [add_monoid ix] : comonad (store ix) :=
  { 
    extract := λ γ ma, ma 0,
    extend := λ α β f ma, (λ x, f (λ y, ma (x + y))),
  }

instance (ix) [add_monoid ix] : is_lawful_comonad (store ix) :=
  {
    extend_extract := λ α₁, by {unfold has_extend.extend has_extract.extract, funext, simp},
    extract_extend := λ α₁ β₁ f, by {unfold has_extend.extend has_extract.extract, funext, simp},
    extend_extend := λ α₁ β₁ γ₁ f g, 
      by {unfold function.comp has_extend.extend has_extract.extract, simp_rw add_assoc},
    map_const_eq := λ α β, rfl,
    id_map := λ α ma, left_id ma,
    comp_map := λ α β γ g h ma, rfl,
  }

structure aMatrix (n m : ℕ) α : Type := 
  {
    data : array (n * m) α
  }

example (x y z) : x ≤ y → z * x ≤ z * y := by {exact nat.mul_le_mul_left z}

def aMatrix.read.aux {n m : ℕ} (x : fin n) (y : fin m) : fin (n * m) :=
  ⟨m * x.val + y.val, by {
    cases x; cases y,
    refine (eq.refl (m * x_val + y_val < n * m)).mpr _,
    cases n, {cases x_property},
    cases m, {cases y_property},
    calc m.succ * x_val + y_val = m*x_val + x_val + y_val : by {rw nat.succ_mul}
      ... ≤ m*n + n + m : by {
        apply add_le_add,
        apply add_le_add,
        apply nat.mul_le_mul_left,
        exact nat.lt_succ_iff.mp x_property,
        exact nat.lt_succ_iff.mp x_property,
        exact nat.lt_succ_iff.mp y_property,
      }
      ... = (m+1) * (n+1) - 1 : by ring
      ... < (m+1) * (n+1) : _
      ... = m.succ * n.succ : rfl
      ... = n.succ * m.succ : mul_comm _ _,
    {
      apply buffer.lt_aux_2,
      ring,
      calc (n + 1) * m + (n + 1) = ((n + 1) * m + n) + 1 : by ring
        ... > 0 : nat.succ_pos _,
    },
  }⟩ 

def aMatrix.read {n m : ℕ} {α} (M : aMatrix n m α) (x : fin n) (y : fin m) : α :=
  M.data.read (aMatrix.read.aux x y)

example (x n m : ℕ ) : m > 0 →  x < m * n → x / m < n := 
by {
  intros,
  exact nat.div_lt_of_lt_mul ᾰ_1
}  

example (x y : ℕ) : y > 0 → x % y < y := by {intros, exact nat.mod_lt x ᾰ} 

def aMatrix.unread {α} {n m : ℕ} (f : fin n → fin (m+1) → α) : aMatrix n (m+1) α := 
  {data := ⟨
    λ ix : fin (n * (m+1)),
      let x : fin n := ⟨ix.val / (m+1), by {cases ix, simp, apply nat.div_lt_of_lt_mul, rw mul_comm, assumption}⟩ in
      let y : fin (m+1) := ⟨ix.val % (m+1), nat.mod_lt ix.val (nat.succ_pos _)⟩ in  
      f x y
  ⟩}

instance {n m : ℕ} : is_lawful_comonad (aMatrix n.succ m.succ) :=
  { 
    map := λ α β f M, {data := f <$> M.data},
    map_const := λ α β b M, {data := {data := λ _, b}},
    extract := λ α ma, ma.read 0 0,
    extend := λ α β f ma, aMatrix.unread (λ x y, f (aMatrix.unread (λ x₂ y₂, ma.read (x + x₂) (y + y₂)))),
    map_const_eq := λ α β, by {funext, cases M, cases M, library_search},
    id_map := _,
    comp_map := _,
    extend_extract := _,
    extract_extend := _,
    extend_extend := _ 
  }
