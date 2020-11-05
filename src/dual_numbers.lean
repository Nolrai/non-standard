import algebra.ring
import algebra.field
import algebra.order
import order.lexicographic
import analysis.calculus.deriv

structure dual (α : Type) := (st : α) (nst : α)

instance dual.of_α (α) [ring α] : has_coe α (dual α) := ⟨λ s, ⟨s, 0⟩⟩

section

variable {α : Type}

def equiv_α_prod : dual α ≃ (α × α) :=
{ to_fun := λ z, ⟨z.st, z.nst⟩,
  inv_fun := λ p, ⟨p.1, p.2⟩,
  left_inv := λ ⟨x, y⟩, rfl,
  right_inv := λ ⟨x, y⟩, rfl }

theorem ext : ∀ {z w : dual α}, z.st = w.st → z.nst = w.nst → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

instance [has_zero α] : has_zero (dual α) := ⟨⟨0, 0⟩⟩

def d [ring α] : dual α := ⟨0, 1⟩

def dual.add [ring α] : dual α → dual α → dual α
  | a b := ⟨a.st + b.st, a.nst + b.nst⟩

theorem ext_iff {z w : dual α} : z = w ↔ z.st = w.st ∧ z.nst = w.nst := ⟨λ H, by simp [H], and.rec ext⟩

instance [ring α] : has_coe α (dual α) := ⟨λ r, ⟨r, 0⟩⟩

def dual.mul [ring α]
: dual α → dual α → dual α
  | a b := ⟨a.st + b.st, a.st * b.nst + a.nst * b.st⟩

instance [has_le α] [ring α] : has_le (dual α) :=
  { le := λ a b, (⟨a.st, a.nst⟩ : lex α α)  ≤ (⟨b.st, b.nst⟩ : lex α α)  }

instance [preorder α] [ring α] : preorder (dual α) := 
  {
    le := has_le.le,
    le_refl := λ a, by {have h : (⟨a.st, a.nst⟩ : lex α α) ≤ ⟨a.st, a.nst⟩ , by apply le_refl, },
    le_trans := λ a b c ab bc, 
      begin 
        have h : (⟨a.st, a.nst⟩ : lex α α) ≤ ⟨c.st, c.nst⟩,
        by {
          transitivity (⟨b.st, b.nst⟩ : lex α α);
          unfold preorder.le has_le.le;
          split; 
          cases ab; cases bc;
          simp; assumption
        },
        apply h,
      end
  }

instance [partial_order α] [ring α] : partial_order (dual α) :=
  {
    le := has_le.le,
    le_antisymetry := begin  end
  }

end