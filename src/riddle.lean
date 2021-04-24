import data.fintype.basic
import control.monad.basic
import data.multiset
import data.rat
import order.bounded_lattice
import order.complete_lattice
import algebra.big_operators.ring
import algebra.big_operators.order

open_locale big_operators

inductive sex 
| girl : sex
| boy : sex

open sex

instance : fintype sex := 
  { 
    elems := 
      ⟨
        [ girl
        , boy
        ], 
        by {simp}
      ⟩,
    complete := λ x, by {cases x; simp} 
  }

inductive day_of_week
| Sunday  
| Monday  
| Tuesday  
| Wednesday
| Thursday
| Friday
| Saturday

open day_of_week

def day_of_week.from_sunday : day_of_week → fin 6
  | Sunday    := 0
  | Monday    := 1
  | Tuesday   := 2
  | Wednesday := 3
  | Thursday  := 4
  | Friday    := 5
  | Saturday  := 6

lemma from_sunday_bijection (x y : day_of_week) : 
  x.from_sunday = y.from_sunday ↔ x = y :=
by {
  cases x; cases y; simp; apply_instance
}

instance : fintype day_of_week := 
  { 
    elems := 
      ⟨
        [ Sunday
        , Monday  
        , Tuesday  
        , Wednesday
        , Thursday
        , Friday
        , Saturday
        ], 
        by {simp}
      ⟩,
    complete := λ x, by {cases x; simp} 
  }

instance {α} (event : α → bool) : decidable_pred ↑event :=
  λ a : α,
    if H : event a
      then is_true H
      else is_false H

def prob {α} (event : α → bool) (situation : multiset α) : ℚ :=
  rat.mk (situation.filter ↑event).card situation.card

lemma prob_def {α} (event : α → bool) (situation : multiset α) :
  prob event situation = rat.mk (situation.filter ↑event).card situation.card := rfl

lemma prob_nonneg {α} (event : α → bool) (situation : multiset α) :
  0 ≤ prob event situation :=
by {
  unfold prob,
  have H : decidable (↑(multiset.card situation) = (0 : ℤ)) := by apply_instance,
  cases H,
  {
    have : (0 : ℤ) ≤ ↑(multiset.card situation) := by apply int.coe_zero_le,
    rw ← rat.nonneg_iff_zero_le,
    rw rat.mk_nonneg,
    have : 0 ≤ multiset.card (multiset.filter ↑event situation) := zero_le _,
    clear H, exact int.coe_zero_le _,
    rw le_iff_lt_or_eq at this,
    cases this, {exact this}, {exfalso, apply H, symmetry, exact this},
  },
  {
    rw H,
    apply le_of_eq,
    apply rat.mk_zero (multiset.card (multiset.filter ↑event situation)),
  }
}

def prob_given {α : Type} (event : α → bool) (given : α → bool) (situation : multiset α) :=
  rat.mk (situation.filter ↑(event ⊓ given)).card (situation.filter ↑given).card

lemma bool.pi.coe_top (α : Type) : ∀ a, (↑(⊤ : α → bool) : α → Prop) a := 
by {
  intros,
  unfold_coes,
  unfold_projs,
  simp only [top_eq_tt, eq_self_iff_true],
}

lemma multiset.filter_top {α : Type} (m : multiset α) : m.filter ↑(⊤ : α → bool) = m := 
by {
  induction m,
  unfold multiset.filter,
  rw quot.lift_on_mk,
  {
    have : ∀ l : list α, l.filter ↑(⊤ : α → bool) = l,
    {
      clear m,
      intros l,
      induction l,
      case nil {
        refine list.filter_nil _
      },
      case cons {
        transitivity l_hd :: l_tl.filter ↑⊤,
        apply list.filter_cons_of_pos,
        apply bool.pi.coe_top,
        congr, exact l_ih
      }
    },
    rw this, apply (multiset.quot_mk_to_coe'' _).symm
  },
  case h {refine rfl},
}

lemma prob_eq_prob_given_top {α} (event : α → bool) (situation : multiset α) :
  prob event situation = prob_given event ⊤ situation := 
by {
  unfold prob prob_given,
  congr,
  apply inf_top_eq.symm,
  apply (multiset.filter_top _).symm,
}

example (q : ℚ) : q ≠ 0 → q/q = 1 := by {intros, exact div_self ᾰ}

example (z : ℤ) : z ≠ 0 → rat.mk z z = 1 := by 
  {intros z_nonzero, rw rat.mk_eq_div, apply div_self, exact int.cast_ne_zero.mpr z_nonzero}

example (n : ℕ) : (↑n : ℚ) = ↑(↑n : ℤ) := by {intros, exact (int.cast_coe_nat n).symm}

lemma aux (a b : ℚ) : b > 0 → a + b = 0 → a < 0 := 
by { 
  intros b_gt_z add_eq_0,
  have H : a < 0 ∨ a = 0 ∨ a > 0 := by {exact trichotomous a 0},
  cases H, {exact H},
  exfalso, apply gt_irrefl (0 : ℚ),
  cases H,
  {
    rw H at add_eq_0,
    rw zero_add at *,
    rw add_eq_0 at *,
    apply b_gt_z,
  },
  have add_gt_0 : a + b > 0 := add_pos H b_gt_z,
  rw add_eq_0 at add_gt_0,
  assumption,
}

lemma unitarity {α : Type} (s : multiset α) (s_nonempty : s ≠ ∅) : prob ⊤ s = 1 :=
  have H : ↑(multiset.card s) ≠ (0 : ℚ) := 
    ne_of_gt (nat.cast_pos.mpr (multiset.card_pos.mpr s_nonempty)),
  by {
    calc 
      prob ⊤ s  = (rat.mk _ _) : prob_def _ _
      ...       = rat.mk ↑(multiset.card s) ↑(multiset.card s) : by {congr, apply multiset.filter_top}
      ...       = ↑(multiset.card s)/↑(multiset.card s) : rat.mk_eq_div _ _
      ...       = 1 : div_self H
  }

lemma rat.mk_simplify (x y z : ℤ) : x ≠ 0 → rat.mk (y * x) (z * x) = rat.mk y z :=
by {
  intros x_ne_0,
  have z_0 : decidable (z = 0) := by {apply_instance},
  cases z_0,
  case is_true {rw z_0, rw zero_mul, simp_rw [rat.mk_zero]},
  case is_false {
    apply (rat.mk_eq _ z_0).mpr,
    ring,
    apply mul_ne_zero z_0 x_ne_0,
  }
}

lemma multiset.add_coe {α} (l₁ l₂ : list α) : ↑l₁ + ↑l₂ = (↑(l₁ ++ l₂) : multiset α) :=
  by {
    unfold has_add.add,
    unfold multiset.add,
    unfold_coes,
  }

lemma bool.tt_of_inf_left (b₁ b₂ : bool) : b₁ ⊓ b₂ = tt → b₁ = tt := 
by {
  cases b₁; cases b₂; simp,
  suffices : ¬ (tt ≤ ff),
  apply this,
  apply not_le_of_lt,
  exact bool.ff_lt_tt
}

lemma bool.tt_of_inf_right (b₁ b₂ : bool) : b₁ ⊓ b₂ = tt → b₂ = tt := 
by {
  rw inf_comm,
  apply bool.tt_of_inf_left,
}

lemma finite_additivity_aux (b₀ b₁ : bool) : b₀ ⊔ b₁ = tt ↔ b₀ = tt ∨ b₁ = tt :=
by {
  split; intros h,
  {
    have : tt ≤ b₀ ∨ tt ≤ b₁,
    {
      apply le_sup_iff.mp,
      apply le_of_eq,
      symmetry,
      exact h,
      apply_instance,
    },
    {
      have H : ∀ b, tt ≤ b ↔ tt = b := λ b, by {cases b, simp, simp},
      simp_rw eq_comm,
      simp_rw ← H,
      exact this,
    },
  },
  {
    cases h; rw h; simp,
  }
}

lemma finite_additivity (α : Type) (s t : α → bool) (situation : multiset α) (disjoint : s ⊓ t = ⊥) :
  prob (s ⊔ t) situation = prob s situation + prob t situation :=
by {
  simp_rw prob_def,
  set d : ℤ := ↑(multiset.card situation) with d_def,
  have d_zero : decidable (d = 0) := by apply_instance,
  cases d_zero with d_ne_0 d_eq_0,
  case is_false {
    rw rat.add_def,
    ring_nf,
    ring_nf,
    rw pow_two d,
    rw rat.mk_simplify,
    congr,
    rw ← multiset.card_add,
    rw multiset.filter_add_filter,
    have : multiset.filter (λ (a : α), (↑s : α → Prop) a ∧ (↑t : α → Prop) a) situation = 0,
    {
      have : ∀ (a : α), ((↑s : α → Prop) a ∧ (↑t : α → Prop) a) = false,
      {
        intros a,
        transitivity ↥((s ⊓ t) a),
        {
          unfold_coes,
          funext, simp only [inf_apply, eq_iff_iff],
          split; intros h,
          { 
            obtain ⟨h_s, h_t⟩ := h,
            rw h_s, rw h_t,
            rw inf_idem,
          },
          {
            split,
            apply bool.tt_of_inf_left _ _ h,
            apply bool.tt_of_inf_right _ _ h,
          },
        },
        {
          rw disjoint,
          funext, simp only [bot_eq_ff, false_iff, bot_apply, eq_iff_iff, coe_sort_ff],
          apply not_false,
        },
      },
      {
        simp_rw this,
        rw multiset.filter_eq_nil,
        intros _ _,
        apply not_false,
      }
    },
    {
      rw this,
      rw add_zero,
      congr,
      funext,
      unfold_coes,
      simp,
      apply finite_additivity_aux,
    },
    all_goals {exact d_ne_0},
  },
  case is_true {
    rw d_eq_0,
    simp_rw rat.mk_zero,
    symmetry, apply zero_add,
  }
}

structure child := 
  (sex : sex)
  (born_on : day_of_week)

instance : decidable_eq sex 
  | boy   boy   := is_true rfl
  | girl  girl  := is_true rfl
  | boy   girl  := is_false (by {simp})
  | girl  boy   := is_false (by {simp})

instance : decidable_eq day_of_week :=
  by {
    intros x y,
    cases x; cases y; simp; apply_instance
  }

instance : decidable_eq child :=
by {
  intros x y,
  cases x; cases y; simp; apply_instance
}

instance : fintype child :=
by {
  apply fintype.of_surjective (function.uncurry child.mk),
  intros x,
  use (x.1, x.2),
  cases x,
  simp,
}

abbreviation outcome := fin 2 → child

def background : multiset outcome := finset.univ.val

open child

def at_least_one_boy (o : outcome) := to_bool (boy ∈ ([o 1, o 2].map sex))

def riddle0 : ℚ := 
  prob at_least_one_boy background

def both_boys (o : outcome) := to_bool (([o 1, o 2].map sex) = [boy, boy])

def riddle1 : ℚ := 
  prob_given both_boys at_least_one_boy background

def at_least_one_boy_born_on_a_tuesday (o : outcome) := to_bool (child.mk boy Tuesday ∈ [o 1, o 2])

def riddle2 : ℚ :=
  prob_given both_boys at_least_one_boy_born_on_a_tuesday background

#eval riddle0
#eval riddle1
#eval riddle2