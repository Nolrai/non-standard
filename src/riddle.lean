import data.fintype.basic
import control.monad.basic
import data.finsupp
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

def same_ratios (α) (x y : α →₀ ℕ) : Prop :=
  ∀ a b: α, rat.mk (x a) (x b) = rat.mk (y a) (y b)

instance (α) : has_dvd (α →₀ ℕ) :=
  ⟨λ x y, ∃ q : ℚ, 0 < q ∧ ∀ a, rat.mk (x a) (y a) = q ∨ (x a = 0 ∧ y a = 0)⟩

example (a b c : ℤ) : c ≠ 0 → a * c = b * c → a = b := by {intros, exact (mul_left_inj' ᾰ).mp ᾰ_1}

lemma same_ratios_iff_dvd {α} (x y : (α →₀ ℕ)) : x ∣ y ↔ same_ratios α x y :=
by {
  unfold same_ratios,
  unfold has_dvd.dvd,
  split; intros h,
  {
    obtain ⟨q, ⟨q_pos, h⟩⟩ := h,
    have : ∃ (n : ℤ) (d : ℕ) (d_pos : 0 < d) (coprime_abs_n_d : n.nat_abs.coprime d), rat.mk n d = q,
      apply rat.num_denom_cases_on q, intros n d h₀ h₁, use [n, d, h₀, h₁],
    obtain ⟨n, d, d_pos, coprime_abs_n_d, q_eq⟩ := this,
    intros,
    have h_a := h a,
    have h_b := h b,

    -- just so I can tell them appart visually
    set i : ℤ := ↑(x a),
    set j : ℤ := ↑(x b),
    set k : ℤ := ↑(y a),
    set l : ℤ := ↑(y b),
    
    clear h,
    cases h_a; cases h_b; rw ← q_eq at *; clear' q q_eq,
    {
      have : k ≠ 0 := λ h, by {rw h at h_a, rw rat.mk_zero at h_a, rw h_a at q_pos, apply (lt_irrefl _ q_pos)},
      have : n * i * l = n * k * j,
      {
        rw rat.mk_eq at *,
        have : n * i * l * ↑d = n * k * j * ↑d,
        {
          calc n * i * l * ↑d = n * l * i * ↑ d : by {ring_nf}
          ...                 = (n * l) * (i * ↑ d) : by {ring_nf}
          ...                 = (n * l) * (n * k) : by {congr' 1}
          ...                 = n * l * n * k : by {ring_nf}
          ...                 = n * k * n * l : by {ring_nf}
          ...                 = n * k * (n * l) : by {ring_nf}
          ...                 = (n * k) * (j * ↑d) : by {congr' 1, exact h_b.symm}
          ...                 = _ : by {ring_nf}
        },
        {
          apply (mul_left_inj' _).mp this,
          apply int.coe_nat_ne_zero.mpr,
          apply ne_of_gt d_pos,
        },
        
      },
      simp_rw mul_assoc at this,
      apply (mul_right_inj' _).mp this,
      intros n_eq_0,
      rw n_eq_0 at q_pos,
      rw rat.zero_mk at q_pos,
      apply lt_irrefl (0 : ℚ) q_pos,
    },
  }
}  

lemma same_ratios.reflexive {α} [decidable_eq α] : reflexive (same_ratios α) := λ x a b, rfl
lemma same_ratios.symmetric {α} [decidable_eq α] : symmetric (same_ratios α) := λ x y h a b, (h a b).symm
lemma same_ratios.transitive {α} [decidable_eq α] : transitive (same_ratios α) := 
  λ (x y z : α →₀ ℕ) (x_y : same_ratios α x y) (y_z : same_ratios α y z) (a b : α), (x_y a b).trans (y_z a b)

def prob_setoid (α) [decidable_eq α] : setoid (α →₀ ℕ) :=
⟨same_ratios α, mk_equivalence _ same_ratios.reflexive same_ratios.symmetric same_ratios.transitive⟩

-- random variables with probabilities in ℚ
def random_variable (α) [decidable_eq α] := quotient (prob_setoid α)

def finsupp.size {α} (f : α →₀ ℕ) := f.sum (λ _ b, b)

-- for some reason the finsupp.filter is noncomputable.
def finsupp.filter' {α} (s : α →₀ ℕ) (p : α → Prop) [decidable_pred p] : α →₀ ℕ :=
  { finsupp .
    support := s.support.filter p,
    to_fun := λ a : α, if p a then s a else 0,
    mem_support_to_fun := 
      λ a, by {
        rw finset.mem_filter, 
        rw ← eq_iff_iff,
        obtain ⟨supp, f, f_supp_iff⟩ := s,
        simp,
        rw f_supp_iff,
        rw and_comm,
      } 
  }

lemma finsupp.filter'_eq_filter {α} (s : α →₀ ℕ) (p : α → Prop) [decidable_pred p] :
  s.filter' p = s.filter p := 
by {
  obtain ⟨supp, f, f_supp_iff⟩ := s,
  unfold finsupp.filter',
  unfold finsupp.filter,
  simp,
}

lemma support_eq_of_dvd {α} [decidable_eq α] (s t : α →₀ ℕ) : 
  s ∣ t → s.support = t.support :=
by {
  revert t,
  apply finsupp.induction₂ s; clear s,
  {
    intros t zero_dvd_t,
    obtain ⟨q, q_pos, zero_dvd_t⟩ := zero_dvd_t,
    have : ∀ a, t a = 0,
    {
      intros a,
      have H := zero_dvd_t a,
      cases H; simp at H,
      {linarith},
      {exact H}
    },
    ext,
    rw t.mem_support_to_fun,
    rw (0 : α →₀ ℕ).mem_support_to_fun,
    unfold_coes at this,
    rw this, clear this, 
    unfold_projs,
    simp,
  },
  {
    intros f g f_ih g_ih t f_g_dvd_t,
    have : ∃ t₀ t₁, f∣t₀ ∧ g∣t₁ ∧ t₀ + t₁ = t,
    {
      obtain ⟨q, q_pos, q_hyp⟩ := f_g_dvd_t,
      cases f; cases g,
      simp at *,
    }
  }
}

lemma finsupp.filter_div_filter_of_div {α} [decidable_eq α] (s t : α →₀ ℕ) 
  : s ∣ t → ∃ q : ℚ, 0 < q ∧ ∀ p, ↑(s.filter p).size * q = ↑(t.filter p).size  :=
by {
  intros s_dvd_t,
  obtain ⟨q, q_pos, s_dvd_t⟩ := s_dvd_t,
  use [q⁻¹, inv_pos.mpr q_pos],
  intro p,
}

def prob' {α} [decidable_eq α] (event : α → bool) (situation : α →₀ ℕ) : ℚ :=
  rat.mk (situation.filter' ↑event).size situation.size

def prob (α) [decidable_eq α] (event : α → bool) (var : random_variable α) : ℚ  := 
  @quotient.rec_on (α →₀ ℕ) (prob_setoid α) (λ _, ℚ) var (prob' event)
  (λ a b a_r_b, by {simp, unfold prob', })
  
lemma prob_def {α} (event : α → bool) (random_variable : multiset α) :
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

section children

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

end children

section frogs

structure frog := 
  (sex : sex)
  (is_croaking : bool)

variable chance_of_croaking : ℚ



end frogs