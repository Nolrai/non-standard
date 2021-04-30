import control.monad.basic
import linear_algebra.matrix
import algebra.group
import data.nat.basic
import data.array.lemmas
import data.equiv.basic

universes u v

open function

class has_extract (m : Type u → Type u) :=
  (extract : Π {α}, m α → α)

class has_extend (m : Type u → Type u) :=
  (extend : Π {α β}, (m α → β) → m α → m β)

class has_duplicate (m : Type u → Type u) :=
  (duplicate : Π {α}, m α → m (m α))

infixl ` =>> `:55 := flip has_extend.extend

class comonad (m : Type u → Type u) extends functor m, has_extract m, has_extend m, has_duplicate m : Type (u+1) := (duplicate := λ α (ma : m α), ma =>> id)

class is_lawful_comonad m extends comonad m, is_lawful_functor m :=
  (extend_extract : ∀ {α} (ma : m α), ma =>> extract = ma)
  (extract_extend : ∀ {α β} {f : m α → β}, extract ∘ (extend f) = f)
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

open is_lawful_comonad

instance (ix) [add_monoid ix] : is_lawful_comonad (store ix) :=
  {
    extend_extract := λ α₁ ma, by {unfold flip has_extend.extend has_extract.extract, simp},
    extract_extend := λ α₁ β₁ f, by {unfold has_extend.extend has_extract.extract, funext, simp},
    extend_extend := λ α₁ β₁ γ₁ f g, 
      by {unfold function.comp has_extend.extend has_extract.extract, simp_rw add_assoc},
    map_const_eq := λ α β, rfl,
    id_map := λ α ma, left_id ma,
    comp_map := λ α β γ g h ma, rfl,
  }

structure aMatrix (n m : ℕ) α : Type := 
  (flattened : array (n * m) α)

@[ext]
lemma aMatrix.ext {n m : ℕ} {α} {M M' : aMatrix n m α} : M.flattened = M'.flattened → M = M' :=
  λ h, by {cases M; cases M', simp at h, congr, assumption}

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
      ... = (m+1) * (n+1) - 1 : by ring_nf
      ... < (m+1) * (n+1) : _
      ... = m.succ * n.succ : rfl
      ... = n.succ * m.succ : mul_comm _ _,
    {
      apply buffer.lt_aux_2,
      ring_nf,
      calc (n + 1) * m + (n + 1) = ((n + 1) * m + n) + 1 : by ring
        ... > 0 : nat.succ_pos _,
    },
  }⟩ 

def aMatrix.read {n m : ℕ} {α} (M : aMatrix n m α) : store (fin n × fin m) α :=
  λ (p : fin n × fin m), M.flattened.read (aMatrix.read.aux p.1 p.2)

def aMatrix.unread {α} {n m : ℕ} (f : store (fin n × fin m) α) : aMatrix n m α := 
  ⟨⟨
    λ ix : fin (n * m),
      let x : fin n := ⟨ix.val / m, by {cases ix, simp, apply nat.div_lt_of_lt_mul, rw mul_comm, assumption}⟩ in
      have m_pos : 0 < m,
      {
        cases m,
        {rw mul_zero at ix, apply fin_zero_elim ix},
        {apply nat.zero_lt_succ}
      },
      let y : fin m := ⟨ix.val % m, nat.mod_lt ix.val m_pos⟩ in  
      f (x, y)
  ⟩⟩

lemma unread_read_aux (n m : ℕ) (ix : fin (n * m)) (p q) : 
  (aMatrix.read.aux ⟨↑ix / m, p⟩ ⟨↑ix % m, q⟩) = ix :=
by {
  obtain ⟨ix, ix_h⟩ := ix,
  unfold aMatrix.read.aux,
  simp,
  clear p q ix_h,
  exact nat.div_add_mod ix m,
}

@[simp]
lemma unread_read {n m : ℕ} {α} (M : aMatrix n m α) : aMatrix.unread (M.read) = M :=
by {
  cases M; cases M with f,
  unfold aMatrix.read,
  unfold aMatrix.unread,
  congr,
  funext,
  simp,
  rw unread_read_aux,
  unfold array.read d_array.read,
}

lemma cspam {x y m : ℕ} : 0 < m → (y < m ↔ y/m = 0) :=
by {
  intros,
  exact (nat.div_eq_zero_iff ᾰ).symm,
}

lemma cspam2 {x y : ℕ} : x < y → 0 < y := 
  λ h, 
  by {
    cases x, 
    {exact h}, 
    {
      transitivity x.succ,
      {apply nat.zero_lt_succ},
      exact h,
    }
  }

lemma cspam3 {x y z : ℕ} (z_pos : 0 < z) (y_lt_z : y < z) : (z * x + y) / z = x :=
by {
  induction x with x x_ih,
  {
    rw mul_zero,
    rw zero_add,
    apply (nat.div_eq_zero_iff z_pos).mpr y_lt_z,
  },
  {
    calc (z*x.succ + y)/z = (x.succ + y/z) : 
      by {rw add_comm, rw nat.add_mul_div_left, rw add_comm, exact z_pos}
      ... = x.succ + 0 : by {have H : y/z = 0, apply nat.div_eq_zero y_lt_z, rw H}
  }
}

@[simp]
lemma read_unread {n m : ℕ} {α} (f : store (fin n × fin m) α) : (aMatrix.unread f).read = f :=
by {
  funext,
  unfold aMatrix.read,
  unfold aMatrix.unread,
  simp,
  unfold array.read d_array.read,
  obtain ⟨x,y⟩ := p, cases y, cases x,
  simp,
  unfold aMatrix.read.aux, simp,
  have m_pos : 0 < m := cspam2 y_property,
  congr,
  {exact cspam3 m_pos y_property},
  {
    rw nat.add_mod,
    rw nat.mul_mod_right,
    rw zero_add,
    have H : y_val % m = y_val := nat.mod_eq_of_lt y_property,
    simp_rw H,
  },
}

instance {n m : ℕ} : functor (aMatrix n m) :=
  {
    map := λ α β f M, aMatrix.unread (f ∘ M.read),
    map_const := λ α β b M, ⟨⟨λ _, b⟩⟩,
  }

instance {n m : ℕ} : is_lawful_functor (aMatrix n m) :=
  {
    id_map := λ α m, by {unfold_projs, simp,},
    comp_map := λ α β γ g h ma, by {unfold_projs, simp},
  }

instance {n m : ℕ} : comonad (aMatrix n.succ m.succ) :=
  {
    extract := λ α ma, has_extract.extract (ma.read),
    extend := λ α β f ma, aMatrix.unread (ma.read =>> (f ∘ aMatrix.unread)),
  }

lemma aMatrix.extend_extract {n m : ℕ} (α) (ma : aMatrix n.succ m.succ α) : ma =>> has_extract.extract = ma:= 
  by {
    cases ma; cases ma with f,
    unfold1 has_extract.extract, 
    unfold1 has_extend.extend, 
    unfold flip,
    unfold has_extend.extend,
    unfold has_extract.extract,
    simp,
  }

lemma aMatrix.extract_extend {n m : ℕ} {α β : Type} (f : aMatrix n.succ m.succ α → β) :
  has_extract.extract ∘ has_extend.extend f = f :=
by {
  funext,
  unfold_projs,
  unfold flip function.comp,
  simp,
}

lemma aMatrix.extend_extend {n m : ℕ} {α β γ : Type}
  (g : aMatrix n.succ m.succ α → β)
  (h : aMatrix n.succ m.succ β → γ) :
  has_extend.extend h ∘ has_extend.extend g =
    has_extend.extend (h ∘ has_extend.extend g) :=
by {
  unfold comp,
  funext,
  unfold has_extend.extend flip comp,
  simp, 
  funext, congr,
  funext, congr,
  funext, congr' 2,
  funext, congr' 1,
  apply add_assoc,
}

instance {n m : ℕ} : is_lawful_comonad (aMatrix n.succ m.succ) :=
  {
    extend_extract := λ α ma, aMatrix.extend_extract α ma,
    extract_extend := λ α β f, aMatrix.extract_extend f,
    extend_extend := λ α β γ g h, aMatrix.extend_extend g h,
    .. aMatrix.is_lawful_functor,
  }

lemma map_flattened_read {n m α β} (mat : aMatrix n m α) (f : α → β) (i : fin (n * m)) : 
  (f <$> mat).flattened.read i = f (mat.flattened.read i) := 
by {
  obtain ⟨⟨d⟩⟩ := mat,
  unfold_projs,
  unfold array.read d_array.read,
  unfold aMatrix.read aMatrix.unread array.read d_array.read,
  simp,
  rw unread_read_aux,
}

def to_one_zero {α} (p : α → bool) (a : α) : ℕ := if (p a) then 1 else 0
lemma to_one_zero.def {α} (p : α → bool) (a : α) : to_one_zero p a = if (p a) then 1 else 0 := rfl
lemma to_one_zero.is_one_or_zero {α} (p : α → bool) (a : α) : to_one_zero p a = 1 ∨ to_one_zero p a = 0 :=
by {
  rw to_one_zero.def,
  split_ifs; simp
}

def array.count {n} {α} (arr : array n α) (p : α → bool) : ℕ := (arr.map (to_one_zero p) ).foldl 0 (+)

lemma list.one_zero_filter_eq_sum (l : list ℕ) (is_binary : ∀ x, x ∈ l → x = 1 ∨ x = 0) : 
  l.sum = (l.filter (=1)).length :=
by {
  induction l, case nil {simp},
  simp,
  unfold list.filter,

  have l_tl_is_binary : ∀ x, x ∈ l_tl → x = 1 ∨ x = 0 := 
    λ (x : ℕ) (x_in_l_tl : x ∈ l_tl), is_binary x (list.mem_cons_of_mem l_hd x_in_l_tl),
  have l_ih' := l_ih l_tl_is_binary, clear l_ih, rename l_ih' l_ih, clear l_tl_is_binary,

  have l_hd_is : l_hd = 1 ∨ l_hd = 0 := is_binary l_hd (list.mem_cons_self l_hd l_tl),
  cases l_hd_is; rw l_hd_is; clear l_hd_is,
  {
    rw if_pos,
    unfold list.length,
    transitivity l_tl.sum + 1, {apply add_comm},
    congr, 
    apply l_ih,
    refl,
  },
  {
    rw if_neg,
    transitivity l_tl.sum, {apply zero_add},
    apply l_ih,
    apply zero_ne_one,
  }
}

lemma array.map_image {n α β} (f : α → β) (arr : array n α) (ix) : (arr.map f).read ix ∈ f '' (∈ arr) :=
by {
  rw array.read_map,
  apply set.mem_image_of_mem,
  use ix,
}

lemma list.length_filter_le {α} {l : list α} {p} [decidable_pred p] : (l.filter p).length ≤ l.length :=
by {
  induction l,
  {simp},
  cases (_inst_1 l_hd) with is_not_p is_p,
  {
    rw list.filter_cons_of_neg _ is_not_p,
    transitivity l_tl.length, {exact l_ih},
    apply nat.le.intro rfl,
  },
  {
    rw list.filter_cons_of_pos _ is_p,
    simp_rw list.length_cons,
    apply (add_le_add_iff_right 1).mpr l_ih,
  }
}

lemma array.count_le_size {n α} (arr : array n α) (p) : arr.count p ≤ n :=
by {
  unfold array.count,
  rw ← array.to_list_foldl,
  simp_rw add_comm,
  calc list.foldl has_add.add 0 (arr.map (to_one_zero p)).to_list
          = ((arr.map (to_one_zero p)).to_list).sum : by {unfold list.sum,}
      ... = (((arr.map (to_one_zero p)).to_list).filter (=1)).length : _
      ... ≤ (arr.map (to_one_zero p) ).to_list.length : by apply list.length_filter_le
      ... = n : by {apply array.to_list_length},
  {
    apply list.one_zero_filter_eq_sum,
    intros x,
    rw array.mem_to_list,
    rw array.mem.def,
    rintros ⟨ix, ix_h⟩,
    have : x ∈ (to_one_zero p) '' set.univ,
    { 
      have : ((to_one_zero p) '' (∈ arr)) ⊆ (to_one_zero p) '' set.univ :=
        set.image_subset _ (set.subset_univ _),
      apply set.mem_of_subset_of_mem this, clear this,
      rw ← ix_h,
      apply array.map_image,
    },
    rw set.mem_image at this,
    obtain ⟨b, ⟨b_univ,b_h⟩⟩ := this, clear b_univ,
    rw ← b_h,
    apply to_one_zero.is_one_or_zero,
  },
}

-- 2D boolean outer-totalistic rules (life-alikes)
def lifeLike {n m k : ℕ} 
  (neiboorhood : aMatrix (n+1) (m+1) bool → array k bool) 
  (survive birth : list (fin (k + 1))) : 
  aMatrix (n+1) (m+1) bool → aMatrix (n+1) (m+1) bool :=
  has_extend.extend 
    (λ m,
      have the_count : fin (k + 1) := 
        ⟨(neiboorhood m).count (= tt), nat.lt_succ_iff.mpr (array.count_le_size (neiboorhood m) _)⟩,
      let update := 
        if m.read (0, 0)
        then survive
        else birth in
      if the_count ∈ update
        then tt else ff
    )
    
def moore_neighborhood {n m : ℕ} {α} (mx : aMatrix (n+1) (m+1) α) : array 8 α :=
  let indecies : list (fin (n+1) × fin (m+1)) := 
    [
      (-1, -1), (-1,  0), (-1, 1),
      ( 0, -1),           ( 0, 1), -- skip the cell itself
      ( 1, -1), ( 1,  0), ( 1, 1)
    ] in
  indecies.to_array.map mx.read 


def life {n m} : aMatrix (n+1) (m+1) bool → aMatrix (n+1) (m+1) bool :=
  lifeLike moore_neighborhood [2,3] [3]

namespace wireworld

inductive cell : Type
  | wall : cell
  | wire : cell
  | head : cell
  | tail : cell

instance : decidable_eq cell := λ a b, 
  by {
   cases a; cases b; simp; try {apply decidable.true}; apply decidable.false,
  }

open cell

def local_update {n m : ℕ} (mx : aMatrix (n+1) (m+1) cell) : cell :=
  match mx.read (0, 0) with
  | wall := wall
  | head := tail
  | tail := wire
  | wire := 
    let the_count := (moore_neighborhood mx).count (= head) in
      if the_count = 1 ∨ the_count = 2
        then head
        else wire  
  end

def update {n m : ℕ} (mx : aMatrix (n+1) (m+1) cell) : aMatrix (n+1) (m+1) cell :=
  mx =>> local_update

end wireworld

-- like wire world but bistable and reversable.
section flowgate

inductive wire 
  | low
  | rising
  | high
  | falling

open equiv
open wire

instance : decidable_eq wire := λ a b, 
  by {
   cases a; cases b; simp; try {apply decidable.true}; apply decidable.false,
  }

def wire.succ : wire → wire
  | low := rising
  | rising := high
  | high := falling
  | falling := low

def wire.pred : wire → wire
  | low := falling
  | rising := low
  | high := rising
  | falling := high

def forward : perm wire :=
  {
    to_fun := wire.succ,
    inv_fun := wire.pred,
    left_inv := λ x, wire.cases_on x rfl rfl rfl rfl,
    right_inv := λ (x : wire), wire.cases_on x rfl rfl rfl rfl,
  }

abbreviation cell := option wire
  
def backward : perm wire := forward.symm

lemma map_perm_aux {F α} [functor F] [is_lawful_functor F] 
  {f g : α → α} {m : F α} (f_g : ∀ x, f (g x) = x) :
  f <$> g <$> m = m :=
by {
  rw functor.map_map, 
  unfold comp,
  transitivity (id <$> m),
  congr, funext,
  rw f_g, unfold id,
  rw functor.map_id,
  unfold id,
}

def map_perm {F α} [functor F] [is_lawful_functor F] : perm α → perm (F α)
  | ⟨f, g, g_f, f_g⟩ :=
    {
      to_fun := λ x : F α, f <$> x,
      inv_fun := λ x : F α, g <$> x,
      left_inv := λ x : F α, by {simp only, apply map_perm_aux g_f, apply _inst_2},
      right_inv := λ x : F α, by {simp only, apply map_perm_aux f_g, apply _inst_2},
    }

def local_update {n m} (mat : aMatrix (n+1) (m+1) cell) : perm cell := 
  match mat.read 0 with
  | none := 1
  | some w :=
      let the_count := (moore_neighborhood mat).count (∈ [rising, falling].map some) in
      if the_count = 1 ∨ the_count = 2
        then map_perm forward
        else 1
  end

def aMatrix.zip_with {n m} {α β γ} 
  (m₁ : aMatrix n m α) (f : α → β → γ) (m₂ : aMatrix n m β)
  : aMatrix n m γ
  :=
    let a₁ := m₁.flattened in 
    let a₂ := m₂.flattened in 
    aMatrix.mk ⟨λ ix, f (a₁.read ix) (a₂.read ix)⟩

def global_update {n m} (t_minus t_zero : aMatrix (n+1) (m+1) cell)
  : aMatrix (n+1) (m+1) cell :=
  (t_zero =>> local_update).zip_with (λ f a, f $ a) t_minus

abbreviation wire' := array 2 wire

abbreviation cell' := option wire'

def scrape {n m} (mat : aMatrix (n+1) (m+1) cell')
  : aMatrix (n+1) (m+1) cell := 
  (functor.map (λ arr : array _ _, arr.read 1) : cell' → cell) <$> mat

end flowgate
