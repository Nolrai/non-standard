import computability.partrec
import computability.partrec_code
import computability.primrec
import computability.tm_to_partrec
import order.lexicographic

def ack : ℕ → ℕ → ℕ 
  | 0 n := n + 1
  | (m+1) 0 := ack m 1
  | (m+1) (n+1) := ack m (ack (m+1) n)

@[simp]
lemma ack_0 {n} : ack 0 n = n +1 := by {unfold ack}

@[simp]
lemma ack_succ_0 (m) : ack (m+1) 0 = ack m 1 := by {unfold ack}

-- Don't add the third case or simp will take a super long time

abbreviation Γ : unit → Type := λ _, ℕ 

open turing
open turing.TM2
open turing.TM2.stmt

section util
universes u₁ u₂ u₃ u₄

notation `𝔹` := bool 
notation `⋆` := unit.star

def write_to_m : (ℕ × ℕ × 𝔹) → option ℕ → (ℕ × ℕ × 𝔹)
  | ⟨m, n, _⟩ none := ⟨m, n, tt⟩
  | ⟨m, n, b⟩ (some m') := ⟨m', n, b⟩

@[simp]
lemma write_to_m.none (m n b) : write_to_m ⟨m, n, b⟩ none = ⟨m, n, tt⟩ := rfl

@[simp]
lemma write_to_m.some (m n b m') : write_to_m ⟨m, n, b⟩ (some m') = ⟨m', n, b⟩ := rfl 

def write_to_n : (ℕ × ℕ × 𝔹) → option ℕ → (ℕ × ℕ × 𝔹)
  | ⟨m, n, _⟩ none := ⟨m, n, ff⟩
  | ⟨m, n, b⟩ (some n') := ⟨m, n', b⟩

@[simp]
lemma write_to_n.none (m n b) : write_to_n ⟨m, n, b⟩ none = ⟨m, n, ff⟩ := rfl

@[simp]
lemma write_to_n.some (m n b n') : write_to_n ⟨m, n, b⟩ (some n') = ⟨m, n', b⟩ := rfl

abbreviation get_m (x : ℕ × ℕ × 𝔹) : Γ ⋆ := x.1
abbreviation get_n (x : ℕ × ℕ × 𝔹) : Γ ⋆ := x.2.1

abbreviation get_has_failed (x : ℕ × ℕ × 𝔹) : 𝔹 := x.2.2

abbreviation get_is_m_zero (x : ℕ × ℕ × 𝔹) : 𝔹 := x.1 = 0
abbreviation get_is_n_zero (x : ℕ × ℕ × 𝔹) : 𝔹 := x.2.1 = 0

abbreviation get_succ_n (x : ℕ × ℕ × 𝔹) : Γ ⋆ := nat.succ x.2.1
abbreviation get_pred_m (x : ℕ × ℕ × 𝔹) : Γ ⋆ := nat.pred x.1
abbreviation get_pred_n (x : ℕ × ℕ × 𝔹) : Γ ⋆ := nat.pred x.2.1

abbreviation recurse : TM2.stmt Γ unit (ℕ × ℕ × 𝔹) := load (λ _, (0,0, ff)) $ goto (λ_, ⋆)
abbreviation ack_tm_type := unit → turing.TM2.stmt Γ unit (ℕ × ℕ × 𝔹)
abbreviation ack_cfg := TM2.cfg Γ unit (ℕ × ℕ × 𝔹)

def mk_cfg (n m : ℕ) (l : list ℕ) : ack_cfg := TM2.cfg.mk (some ⋆) (n, m, ff) (λ _, l)

def ack_tm : ack_tm_type
  | _ :=
    pop ⋆ write_to_n $
      pop ⋆ write_to_m $
        branch get_has_failed (push ⋆ get_n $ halt) $
        branch get_is_m_zero (push ⋆ get_succ_n recurse) $
          push ⋆ get_pred_m $  
            branch get_is_n_zero 
              (push ⋆ (λ _, cast rfl (1:nat)) recurse)
              (push ⋆ get_m $ push ⋆ get_pred_n recurse)

instance pi_type_has_emptyc {T: Type u₁} {K : T → Type} [∀ t : T, has_emptyc (K t)] : has_emptyc (∀ t, K t)
  := ⟨λ _, ∅⟩

@[simp]
lemma empty_pi_type_rec {T: Type u₁} {K : T → Type} [∀ t : T, has_emptyc (K t)] (t : T) : (∅ : ∀ t, K t) t = ∅ := rfl

lemma stack_has_args (i k n₁ n₂ m₁ m₂ : ℕ) (l : list ℕ) : 
  TM2.step ack_tm (mk_cfg n₁ m₁ (i :: k :: l)) = TM2.step ack_tm (mk_cfg n₂ m₂ (i :: k :: l)) := 
  begin
    cases l; unfold mk_cfg; simp; unfold ack_tm; simp;
    unfold write_to_m write_to_n; simp,
  end

def init' (l : list ℕ) : ack_cfg := mk_cfg 0 0 l

def stack_reaches (l₁ l₂ : list ℕ) := 
  turing.TM2.reaches ack_tm (init' l₁) (init' l₂)

open relation.refl_trans_gen

@[trans]
lemma reaches.trans (m : ack_tm_type) (x y z : ack_cfg) : reaches m x y → reaches m y z → reaches m x z :=
 relation.refl_trans_gen.trans

@[trans]
lemma stack_reaches.trans (x y z : list ℕ) : stack_reaches x y → stack_reaches y z→ stack_reaches x z :=
begin
  intros xy yz,
  unfold stack_reaches at *,
  transitivity (init' y); assumption
end 

abbreviation ack_reaches (a b : ack_cfg) := b ∈ step ack_tm a

inductive ack_step : (Σ' (ll : list ℕ) (m : ℕ), ℕ) → (Σ' (ll : list ℕ) (m : ℕ), ℕ) → Prop 
  | step_m : ∀ (ll ll' : list ℕ) (m n n' : ℕ), ack_step ⟨ll, m, n⟩ ⟨ll', m.succ, n'⟩
  | step_n : ∀ (ll ll' : list ℕ) (m n : ℕ), ack_step ⟨ll, m, n⟩ ⟨ll', m, n.succ⟩
  
abbreviation ack_ord := tc ack_step

lemma ack_ord.m (ll m) : ack_ord ⟨ll, ⟨m, 1⟩⟩ ⟨ll, ⟨m + 1, 0⟩⟩ :=
  begin
    constructor,
    constructor,
  end

-- instance ack_ord.has_well_founded : has_well_founded (Σ' (ll : list ℕ) (m : ℕ), ℕ) :=
--   ⟨ack_ord, sorry⟩

lemma ack_ind  (P : ℕ → ℕ → Prop)   (P_0 : ∀ n, P 0 n)
  (P_m : ∀ m, P m 1 → P m.succ 0) 
  (P_n : ∀ m, (∀ n, P m n) → ∀ n, P m.succ n → P m.succ n.succ) (m n : ℕ) : P m n :=
  begin
    revert n,
    induction m,
    case nat.zero {apply P_0},

    case nat.succ {
      rename m_n m,
      intro n,
      induction n,
      case nat.zero {apply P_m, apply m_ih},
      rename n_n n,
      refine P_n _ m_ih _ n_ih,
    }

  end

open relation

lemma ack_tm_correct_aux : ∀ ll, ∀ m n : ℕ, stack_reaches (n :: m :: ll) (ack m n :: ll) :=
  begin
    intros,
    revert m n ll,
    apply ack_ind (λ m n, ∀ ll, stack_reaches (n :: m :: ll) (ack m n :: ll) ),

    {
      intros,
      apply refl_trans_gen.single,
      simp,
      unfold init' mk_cfg step ack_tm,
      simp,
      funext,
      induction a,
      simp,
    },

    {
      intros,
      transitivity (1 :: m :: ll),
      {
        apply refl_trans_gen.single,
        unfold init' mk_cfg step ack_tm,
        simp,
        rw if_neg (nat.succ_ne_zero m),
        congr,
        funext,
        induction a,
        simp,
        refl,
      },
      {
        apply a,
      },
    },

    {
      simp,
      intros m H_m n H_n ll,
      transitivity (n :: m.succ :: m :: ll),
      
      {
        apply refl_trans_gen.single,
        unfold init' mk_cfg step ack_tm,
        simp,
        rw if_neg (nat.succ_ne_zero m),
        rw if_neg (nat.succ_ne_zero n),
        congr,
        funext,
        induction a,
        simp,
        split; refl,
      },

      transitivity (ack m.succ n :: m :: ll),
      apply H_n,
      apply H_m,
    },
  end

local infix `++` := string.append

instance : has_repr ack_cfg :=
  ⟨λ ⟨a, s, c⟩ , "{" ++ repr a ++ ", " ++ repr s ++ ", " ++ repr (c ⋆) ++ "}"⟩

end util

open relation

theorem ack_tm_correct (m n : ℕ) : [ack m n] ∈ TM2.eval ack_tm ⋆ [n, m] :=
  begin
    unfold TM2.eval,
    have H : (eval (step ack_tm) (init' [n, m])) = (eval (step ack_tm) (init' [ack m n])),
    by {
      apply turing.reaches_eval,
      have H := ack_tm_correct_aux [] m n,
      unfold stack_reaches at H,
      unfold TM2.reaches at H,
      unfold turing.reaches,
      apply cast _ H,
      clear H,
      congr,
    },

    have init'_eq_init : ∀ l, init' l = init ⋆ l,
    {
      intro l,
      unfold init mk_cfg init',
      congr,
      funext u,
      induction u,
      simp,
    },

    rw ← init'_eq_init,
    rw H, clear_except,

    have H : ∀ x : ℕ, [x] = (λ (c : ack_cfg), c.stk ⋆) (⟨none, ⟨0, x, tt⟩, (λ _, [x])⟩),
    {
      intros,
      unfold mk_cfg,
    },
    rw H, clear H,

    apply roption.mem_map,
    simp,
    rw turing.mem_eval,

    split,
    {
      unfold init',
      unfold mk_cfg,
      unfold turing.reaches,
      apply refl_trans_gen.single,
      unfold step,
      congr,
      unfold ack_tm,
      simp,
    },

    {
      unfold TM2.step ack_tm,
    },
  
  end


