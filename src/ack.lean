import computability.partrec
import computability.partrec_code
import computability.primrec
import computability.tm_to_partrec
import data.binnat

def ack : ℕ → ℕ → ℕ 
  | 0 n := n + 1
  | (m+1) 0 := ack m 1
  | (m+1) (n+1) := ack m (ack (m+1) n)

def Γ : unit → Type := λ _, ℕ 

open turing
open turing.TM2
open turing.TM2.stmt

section util
universes u₁ u₂ u₃ u₄

notation `𝔹` := bool 
notation `⋆` := unit.star

def write_to_m : (ℕ × ℕ × 𝔹) → option ℕ → (ℕ × ℕ × 𝔹)
  | ⟨m, n, _⟩ none := ⟨m, n, ff⟩
  | ⟨m, n, b⟩ (some m') := ⟨m', n, b⟩

def write_to_n : (ℕ × ℕ × 𝔹) → option ℕ → (ℕ × ℕ × 𝔹)
  | ⟨m, n, _⟩ none := ⟨m, n, ff⟩
  | ⟨m, n, b⟩ (some n') := ⟨m, n', b⟩

abbreviation get_m (x : ℕ × ℕ × 𝔹) : Γ ⋆ := x.1 

abbreviation get_has_failed (x : ℕ × ℕ × 𝔹) : 𝔹 := not x.2.2

abbreviation get_is_m_zero (x : ℕ × ℕ × 𝔹) : 𝔹 := x.1 = 0
abbreviation get_is_n_zero (x : ℕ × ℕ × 𝔹) : 𝔹 := x.2.1 = 0

abbreviation get_succ_n (x : ℕ × ℕ × 𝔹) : Γ ⋆ := nat.succ x.2.1
abbreviation get_pred_m (x : ℕ × ℕ × 𝔹) : Γ ⋆ := nat.pred x.1
abbreviation get_pred_n (x : ℕ × ℕ × 𝔹) : Γ ⋆ := nat.pred x.2.1

abbreviation recurse : TM2.stmt Γ unit (ℕ × ℕ × 𝔹) := load (λ _, (0,0, true)) $ goto (λ_, ⋆)
abbreviation ack_tm_type := unit → turing.TM2.stmt Γ unit (ℕ × ℕ × 𝔹)
abbreviation ack_cfg := TM2.cfg Γ unit (ℕ × ℕ × 𝔹)

abbreviation mk_cfg (n m : ℕ) (l : list ℕ) : ack_cfg := TM2.cfg.mk (some ⋆) (n, m, tt) (λ _, m :: n :: l)

def ack_tm : ack_tm_type
  | _ :=
    pop ⋆ write_to_m $
      pop ⋆ write_to_n $
        branch get_has_failed (push ⋆ get_m halt) $
        branch get_is_m_zero (push ⋆ get_succ_n recurse) $
          push ⋆ get_pred_m $
            branch get_is_n_zero 
              (push ⋆ (λ _, cast rfl (1:nat)) recurse)
              (push ⋆ get_m $ push ⋆ get_pred_n recurse)

example : ∀ x, nat.succ x ≠ 0 := nat.succ_ne_zero

lemma registers_dont_matter_at_call_site (i n₁ n₂ m₁ m₂ : ℕ) (l : list ℕ) : 
  TM2.step ack_tm (mk_cfg n₁ m₁ (i :: l)) = TM2.step ack_tm (mk_cfg n₂ m₂ (i :: l)) := 
  begin
    cases l; simp; unfold ack_tm; simp;
    unfold write_to_m write_to_n; simp;
    cases m₂; cases m₁,
    case nat.zero nat.zero {
      
    },
  end

lemma ack_tm_correct_aux (nₜ mₜ n₁ m₁: ℕ) (l : list ℕ) : ∃ n₂ m₂ : ℕ, turing.TM2.reaches ack_tm (TM2.cfg.mk (some ⋆) (n₁, m₁, tt) ( λ _, mₜ :: nₜ :: l) : ack_cfg) ((TM2.cfg.mk (some ⋆) (n₁, m₁, tt) ( λ _, mₜ :: nₜ :: l) : ack_cfg))

theorem ack_tm_correct (m n : ℕ) : TM2.eval ack_tm ⋆ [n, m] = (pure ∘ pure) (ack m n) :=
  begin
  end