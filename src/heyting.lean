import order.bounded_lattice

set_option old_structure_cmd true

/-- Set / lattice complement -/
class has_compl (α : Type*) := (compl : α → α)

export has_compl (compl)

postfix `ᶜ`:(max+1) := compl

universes u v
variables {α : Type u} {w x y z : α}

class has_internal_imp (α : Type*) :=
  (imp : α → α → α)

infixr ` ⟶ `:60 := has_internal_imp.imp 

class heyting_algebra α extends bounded_distrib_lattice α, has_compl α, has_internal_imp α :=
  (imp_adjoint : ∀ a b c : α, a ⊓ b ≤ c ↔ a ≤ b ⟶ c)
  (compl_from_imp : ∀ a : α, aᶜ = (a ⟶ ⊥))

export heyting_algebra (imp_adjoint compl_from_imp)

section heyting_algebra
variables [heyting_algebra α]

@[simp] lemma imp_refl : x ⟶ x = ⊤ :=
  begin
    rw le_antisymm_iff,
    split, 
      {exact le_top},
      {
        rw ← imp_adjoint,
        exact inf_le_right
      },
  end

lemma imp_mp : x ⊓ (x ⟶ y) ≤ y :=
  begin
    rw inf_comm,
    rw imp_adjoint,
    reflexivity,
  end

lemma le_imp : x ≤ (y ⟶ x) :=
  begin
    rw ← imp_adjoint,
    exact inf_le_left,
  end

@[simp]
lemma imp_mp_simp : x ⊓ (x ⟶ y) = x ⊓ y := 
  le_antisymm (le_inf inf_le_left imp_mp) (inf_le_inf (le_refl x) le_imp)

lemma imp_app : (x ⟶ y) ⊓ x ≤ y :=
  begin
    rw inf_comm,
    exact imp_mp
  end

@[simp]
lemma imp_app_simp : (x ⟶ y) ⊓ x = y ⊓ x:=
  le_antisymm (le_inf imp_app inf_le_right) (inf_le_inf le_imp rfl.ge)

@[simp]
lemma inf_compl_eq_bot : x ⊓ xᶜ = ⊥ :=
  begin
    rw compl_from_imp,
    exact imp_mp_simp.trans inf_bot_eq,
  end

@[simp] theorem compl_inf_eq_bot : xᶜ ⊓ x = ⊥ :=
  eq.trans inf_comm inf_compl_eq_bot

-- if x has a boolean complement it is unique
theorem compl_unique (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : xᶜ = y :=
  begin
    rw compl_from_imp,
    apply le_antisymm,
    {
      transitivity (⊤ ⊓ (x ⟶ ⊥)),
      have h : (x ⟶ ⊥) = ⊤ ⊓ (x ⟶ ⊥):= top_inf_eq.symm,
      rw ← h,
      reflexivity,
      rw ← s,
      rw inf_sup_right,
      apply sup_le,
      transitivity ⊥,
      apply imp_mp,
      exact bot_le,
      apply inf_le_left,
    },

    {
      rw ← imp_adjoint,
      rw inf_comm,
      rw i,
    }

  end
end heyting_algebra

