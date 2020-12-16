import heyting

set_option old_structure_cmd true

inductive tri 
  | fff : tri
  | mmm : tri
  | ttt : tri

open tri

namespace tri

instance : has_bot tri := ⟨fff⟩

lemma tri.bot_def : ⊥ = fff := rfl

instance : has_top tri := ⟨ttt⟩

lemma tri.top_def : ⊤ = ttt := rfl

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

def le.decidable : decidable_rel le :=
  begin
    unfold decidable_rel,
    intros,
    cases a; cases b; try {right, constructor}; {left; intro h; cases h},
  end

instance : decidable_linear_order tri :=
  {
    le_refl := le.refl,
    le_trans := le.trans,
    le_total := le.total,
    le_antisymm := le.antisymm,
    decidable_le := le.decidable,
    .. tri.has_le,
  }

instance : bounded_lattice tri :=
{
  sup := max,
  le_sup_left := λ a b, le_max_left a b,
  le_sup_right := λ a b, le_max_right a b,
  sup_le := λ a b c ac bc, max_le ac bc,

  inf := min,
  inf_le_left := λ a b, min_le_left a b,
  inf_le_right := λ a b, min_le_right a b,
  le_inf := λ a b c ab ac, le_min ab ac,

  le_top := le.top,
  bot_le := le.bot,

  .. tri.has_bot,
  .. tri.has_top,
  .. tri.decidable_linear_order
}

lemma tri.distrib (x y z : tri) : (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z :=
  begin
    cases x; cases y; cases z; try{rw ← tri.bot_def}; try{rw ← tri.top_def};
    simp only [
      sup_bot_eq, 
      bot_sup_eq, 
      top_sup_eq,
      sup_top_eq,
      bot_inf_eq, 
      inf_bot_eq,
      top_inf_eq,
      inf_top_eq,
      inf_idem, 
      sup_idem
      ],

  end

instance : bounded_distrib_lattice tri :=
  {
    le_sup_inf := tri.distrib,
    .. tri.bounded_lattice,
  }

def tri.compl : tri → tri 
  | fff := ttt
  | _ := fff

def tri.imp : tri → tri → tri
  | fff _   := ttt
  | x fff   := tri.compl x
  | mmm _   := ttt
  | ttt x   := x

@[simp]
lemma tri.bot_imp_top (a) : tri.imp ⊥ a = ⊤ := 
  begin
    cases a; rw tri.bot_def; unfold tri.imp; refl
  end

def tri.compl_from_imp (a : tri) : tri.compl a = tri.imp a ⊥ := 
  begin cases a; rw tri.bot_def; unfold tri.compl tri.imp, end

def tri.imp_adjoint (a b c : tri) : a ⊓ b ≤ c ↔ a ≤ tri.imp b c :=
  begin
    cases a; cases b; cases c,

    all_goals {
      unfold tri.imp,
      try {unfold tri.compl},
      try {rw ← tri.bot_def},
      try {rw ← tri.top_def},
      try {rw bot_inf_eq},
      try {rw inf_bot_eq},
      try {rw top_inf_eq},
      try {rw inf_top_eq},
      try {rw inf_idem},
    },

    all_goals {split},
    all_goals {intro H},
    all_goals {try {apply le_refl}},
    all_goals {try {apply bot_le}},
    all_goals {try {apply le_top}},
    all_goals {cases H},

  end

instance : heyting_algebra tri :=
  {
    compl := tri.compl,
    imp := tri.imp,
    compl_from_imp := λ a, by {apply tri.compl_from_imp},
    imp_adjoint := λ a b c, by {apply tri.imp_adjoint},
    .. tri.bounded_distrib_lattice
  }

end tri