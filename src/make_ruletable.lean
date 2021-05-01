import data.finmap
import .hitchhike
import order.lexicographic
import data.equiv.list

inductive vonNeumann
  | N
  | E
  | S
  | W

open vonNeumann

def vonNeumann.to_fin4 (dir : vonNeumann) : fin 4 :=
  match dir with
  | N := 0
  | E := 1
  | S := 2
  | W := 3
  end

def fin.to_vonNeumann  : fin 4 → vonNeumann
  | ⟨0, _⟩ := N
  | ⟨1, _⟩ := E 
  | ⟨2, _⟩ := S
  | ⟨3, _⟩ := W
  | ⟨n+4, p⟩ := false.rec vonNeumann (not_le.mpr p ((4 : ℕ).le_add_left n))

lemma vonNeumann.aux (x : fin 4) : x.to_vonNeumann.to_fin4 = x :=
  match x with
  | ⟨0, _⟩ := rfl
  | ⟨1, _⟩ := rfl 
  | ⟨2, _⟩ := rfl
  | ⟨3, _⟩ := rfl
  | ⟨n+4, p⟩ := false.rec _ (not_le.mpr p ((4 : ℕ).le_add_left n))
  end

def vonNeumann_fin4 : vonNeumann ≃ fin 4 :=
{ 
  to_fun := vonNeumann.to_fin4,
  inv_fun := fin.to_vonNeumann,
  left_inv := λ x, by {cases x; unfold vonNeumann.to_fin4; refl},
  right_inv := λ x, by {apply vonNeumann.aux}
}

inductive Moore
  | NN
  | NE
  | EE
  | SE
  | SS
  | SW
  | WW
  | NW

  open Moore

def Moore.to_fin8 : Moore → fin 8 
| NN := 0
| NE := 1
| EE := 2
| SE := 3
| SS := 4
| SW := 5
| WW := 6
| NW := 7

def fin.toMoore : fin 8 → Moore 
  | ⟨0, _⟩ := NN
  | ⟨1, _⟩ := NE 
  | ⟨2, _⟩ := EE 
  | ⟨3, _⟩ := SE 
  | ⟨4, _⟩ := SS 
  | ⟨5, _⟩ := SW 
  | ⟨6, _⟩ := WW 
  | ⟨7, _⟩ := NW
  | ⟨n+8, p⟩ := false.rec _ (not_le.mpr p ((8 : ℕ).le_add_left n))

def fin.toMoore.aux : ∀ x : fin 8, x.toMoore.to_fin8 = x 
  | ⟨0, _⟩ := rfl
  | ⟨1, _⟩ := rfl
  | ⟨2, _⟩ := rfl
  | ⟨3, _⟩ := rfl
  | ⟨4, _⟩ := rfl
  | ⟨5, _⟩ := rfl
  | ⟨6, _⟩ := rfl
  | ⟨7, _⟩ := rfl
  | ⟨n+8, p⟩ := false.rec _ (not_le.mpr p ((8 : ℕ).le_add_left n))

def Moore_fin4 : Moore ≃ fin 8 :=
{ 
  to_fun := Moore.to_fin8,
  inv_fun := fin.toMoore,
  left_inv := λ x, by {cases x; unfold Moore.to_fin8; refl},
  right_inv := λ x, by {apply fin.toMoore.aux}
}

class neighborhood (α : Type) :=
  (size : nat)
  (to_ix : α ≃ fin size)
  (rotate_one : α → α)
  (reflect : α → α)

def vonNeumann.rotate_one : vonNeumann → vonNeumann
  | N := E
  | E := S
  | S := W
  | W := N

def vonNeumann.reflect : vonNeumann → vonNeumann
  | E := W
  | W := E
  | x := x

instance : neighborhood vonNeumann := 
  {
    size := 4,
    to_ix := vonNeumann_fin4,
    rotate_one := vonNeumann.rotate_one, 
    reflect := vonNeumann.reflect
  }

def Moore.rotate_one : Moore → Moore
  | NN := NE
  | NE := EE
  | EE := SE
  | SE := SS
  | SS := SW
  | SW := WW
  | WW := NW
  | NW := NN


def Moore.reflect : Moore → Moore
  | NE := NW
  | NW := NE
  | EE := WW
  | WW := EE
  | SE := SW
  | SW := SE
  | x := x

instance : neighborhood Moore :=
{ 
  size := 8,
  to_ix := Moore_fin4,
  rotate_one := Moore.rotate_one,
  reflect := Moore.reflect
}

inductive symmetries
  | none
  | rotate2
  | rotate4
  | rotate8
  | rotate4reflect
  | rotate8reflect
  | reflect
  | permute

structure var_line (n : ℕ) :=
  (name : string)
  (values : finset (fin n))

inductive value (n : nat)
  | var : string → value
  | lit : fin n → value

def value.equiv_sum (n) : (string ⊕ fin n) ≃ value n :=
  {
    to_fun := sum.elim value.var value.lit,
    inv_fun := λ v, value.cases_on v sum.inl sum.inr,
    left_inv := λ x, by {simp, cases x; refl},
    right_inv := λ x, by {simp, cases x; refl},
  }

instance subtype.encodable {α} [encodable α] (p : α → Prop) [decidable_pred p] : encodable (subtype p) := 
{ 
  encode := λ s, encodable.encode s.val,
  decode := λ n, 
    (do
      (a : α) ← encodable.decode α n,
      if h : p a
        then some (⟨a, h⟩ : subtype p)
        else none
    ),

  encodek := by {
    intros,
    obtain ⟨a, h⟩ := a,
    simp,
    rw subtype.encodable._match_1,
    split_ifs, refl,
  }
}

def char.equiv : subtype is_valid_char ≃ char := {
  to_fun := λ ⟨x, p⟩, ⟨x, p⟩,
  inv_fun := λ ⟨x, p⟩, ⟨x, p⟩,
  left_inv := λ ⟨x, p⟩, by {simp, rw char.equiv._match_1, rw char.equiv._match_2},
  right_inv := λ ⟨x, p⟩, by {simp, rw char.equiv._match_2, rw char.equiv._match_1},
}

instance : encodable char := encodable.of_equiv (subtype is_valid_char) char.equiv.symm

def string_list : string ≃ list char := {
  to_fun := string.to_list,
  inv_fun := list.as_string,
  left_inv := string.as_string_inv_to_list,
  right_inv := list.to_list_inv_as_string
}

instance : encodable string := encodable.of_equiv (list char) string_list

instance (n) : encodable (value n) := 
  encodable.of_equiv (string ⊕ fin n) (value.equiv_sum n)
.symm
open value

def linear_order.preimage {α β : Type} (f : α ↪ β) [lo : linear_order β] : linear_order α :=
{
  le := λ x y, f x ≤ f y,

  le_refl := λ x, linear_order.le_refl (f x),

  le_antisymm := λ (x y : α) x_y y_x, function.embedding.injective f (linear_order.le_antisymm (f x) (f y) x_y y_x),

  le_trans := λ (x y z : α), linear_order.le_trans (f x) (f y) (f z),

  le_total := λ (a b : α), linear_order.le_total (f a) (f b),

  decidable_le := λ a b, if h : f a ≤ f b then is_true h else is_false h
}

instance {n} : linear_order (value n) := linear_order.preimage (encodable.encode' (value n))

def transition (nh : Type) [nh_ : neighborhood nh] (num_states : nat) : Type := array (nh_.size + 2) (value num_states)

def transition.orig {nh num_states} [nh_ : neighborhood nh] (arr : transition nh num_states) : value num_states := arr.read 0
def transition.neihborhood {nh num_states} [nh_ : neighborhood nh] (arr : transition nh num_states) (ix : nh) : value num_states :=
  arr.read (neighborhood.to_ix ix)

instance (nh : Type) [nh_ : neighborhood nh] (n : nat) : encodable (transition nh n) :=
  encodable.of_equiv (array (nh_.size + 2) (value n)) (equiv.refl _)

def transition.le {nh : Type} [nh_ : neighborhood nh] {n : nat} : (transition nh n) → (transition nh n) → Prop :=
  (encodable.encode' (transition nh n)) ⁻¹'o (has_le.le : ℕ → ℕ → Prop)

@[simp]
lemma transition.le.def {nh : Type} [nh_ : neighborhood nh] {n : nat} (a b : transition nh n) :
  a.le b = ((encodable.encode' (transition nh n)) ⁻¹'o (has_le.le : ℕ → ℕ → Prop)) a b := rfl

instance (nh : Type) [nh_ : neighborhood nh] (n : nat) : linear_order (transition nh n)  := 
  { 
    le := transition.le,
    le_refl := λ a, by {unfold1 has_le.le, simp},
    le_trans := λ x y z, by {simp, apply le_trans},
    
    le_antisymm := λ x y, 
    by {
      unfold_projs, simp,
      intros x_y y_x, 
      apply function.embedding.injective (encodable.encode' _), 
      exact le_antisymm x_y y_x
    },

    le_total :=  λ x y, by {unfold_projs, simp, apply le_total},
    decidable_le := λ x y,
      if h : encodable.encode' _ x ≤ encodable.encode' _ y
        then is_true h
        else is_false h,
    decidable_eq := λ x y,
    if h : encodable.encode' _ x = encodable.encode' _ y
        then is_true (function.embedding.injective (encodable.encode' _) h)
        else is_false (λ x_eq_y : x = y, by {apply h, congr, exact x_eq_y}),
    decidable_lt := λ x y,
    if h : encodable.encode' _ x < encodable.encode' _ y
        then is_true h
        else is_false h,
  }

infix `~>`:40 := λ α β, finmap (λ _ : α, β)

structure rule_table (nh : Type) [h : neighborhood nh] :=
  (n_states : nat)
  (symmetries: symmetries)
  (vars : string ~> (fin n_states))
  (transitions : rbtree (transition nh n_states))

