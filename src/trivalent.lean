import heyting

set_option old_structure_cmd true

inductive tri 
  | fff : tri
  | mmm : tri
  | ttt : tri

open tri

namespace tri

instance : has_bot tri := ⟨fff⟩
instance : has_top tri := ⟨ttt⟩

inductive le : tri → tri → Prop
  | bot : ∀ x, le ⊥ x
  | refl : ∀ x, le x x
  | top : ∀ x, le x ⊤

instance : has_le tri := ⟨le⟩

lemma le.trans (x y z : tri) (xy : x ≤ y) (yz : y ≤ z) : x ≤ z :=
  begin
    cases x; cases y; cases z; cases xy; cases yz; constructor,
  end

lemma le.total (a b : tri) : a ≤ b ∨ b ≤ a :=
  begin
    cases a; cases b; unfold has_le.le; try {left; constructor}; try {right; constructor}
  end

lemma le.antisymm (a b : tri) : a ≤ b → b ≤ a → a = b :=
  begin
    intros ab ba,
    cases ab; cases ba; refl,
  end

instance : linear_order tri :=
  {
    le_refl := le.refl,
    le_trans := le.trans,
    le_total := le.total,
    le_antisymm := le.antisymm,
    .. tri.has_le,
  }

end tri