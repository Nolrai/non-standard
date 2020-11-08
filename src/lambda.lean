import tactic
import data.int.basic
import data.string.basic
universe u

section cs_algebra

end cs_algebra

section untyped

structure fresh (α : Type) : Type := (s : ℕ → α) (injective : ∀ i j, s i = s j → i = j)

def index (n : ℕ) : Type := {z : ℤ // z < n}

inductive lambda : ℕ → Type
  | var {n} : index n → lambda n
  | app {n} : lambda n → lambda n → lambda n
  | abs {n} : lambda (n+1) → lambda n

open lambda

def lambda.sizeof₀ : ∀ {n}, lambda n → ℕ
  | _ (var _) := 0
  | _ (app l r) := 1 + l.sizeof₀ + r.sizeof₀
  | _ (abs body) := 1 + body.sizeof₀

def rename (j : ℕ) : ∀ (i : ℕ) {k} (a : lambda (i + k)), lambda (i + k + j) 
  | i k (var ⟨val, prop⟩) :=
    if val < i
      then var ⟨val, begin apply lt_of_lt_of_le, apply prop, simp end⟩
      else var ⟨val + j, begin simp, exact prop end⟩

  | i k (abs body) :=
    have H : body.sizeof₀ < (body.abs).sizeof₀ := lt_one_add (lambda.sizeof₀ body),
    begin
      apply lambda.abs,
      have H : (i + k + j + 1 = i + (k + 1) + j), by omega, rw H, clear H,
      apply rename,
      apply body,
    end

  | i k (app l r) := 
  have Hᵣ : r.sizeof₀ < (l.app r).sizeof₀, 
    by {unfold lambda.sizeof₀, omega},
  have Hₗ : l.sizeof₀ < (l.app r).sizeof₀, 
    by {unfold lambda.sizeof₀, omega},
  app (rename i l) (rename i r)

  using_well_founded 
    {rel_tac := λ _ _, `[ exact ⟨_, measure_wf (λ (x : Σ' i k, lambda (i + k)), lambda.sizeof₀ x.2.2) ⟩ ]}

/-
non-exhaustive match, the following cases are missing:
lambda.closure_aux i j (var ⟨int.of_nat _, _⟩)
lambda.closure_aux i j (var ⟨-[1+ _], _⟩)
lambda.closure_aux i j (abs _)
-/

lemma aux_aux (a b : ℤ) (h : a < b + 1) : a - 1 < b :=
  begin
    omega
  end

lemma aux {i j : ℕ} {v : ℤ}
  (v_lt : v < ↑(i + j + 1)) :
  v - 1 < ↑(i + j) :=
begin
  apply aux_aux,
  simp at *,
  exact v_lt,
end

lemma aux3 {i k : ℤ} (j) (h_lt : i < j) (h_le : j ≤ k) : i < k :=
  begin
    apply lt_of_lt_of_le h_lt h_le,
  end

def closure_aux (i : ℕ) (b : lambda i) : ∀ {j}, lambda (i + j + 1) → lambda (i + j)
  | j (app l r) :=
    have h_l : l.sizeof₀ < (l.app r).sizeof₀,
      by {
        unfold lambda.sizeof₀,
        linarith
      },
    have h_r : r.sizeof₀ < (l.app r).sizeof₀,
      by {
        unfold lambda.sizeof₀,
        linarith
      },
    app (closure_aux l)  (closure_aux r)
  | j (abs body) := 
    have H : body.sizeof₀ < body.abs.sizeof₀ := lt_one_add (lambda.sizeof₀ body),
    let body' : lambda (i + (j + 1) + 1) := cast rfl body in
    abs $ closure_aux body'
  | j (var ⟨v, v_lt⟩) :=
    decidable.lt_by_cases v  i 
      (λ h_lt, var ⟨v, lt_of_lt_of_le h_lt (by simp)⟩)
      (λ h_eq, @rename _ _ 0 b)
      (λ h_gt, var ⟨v - 1, (begin apply (aux v_lt), end)⟩)
  using_well_founded 
    {rel_tac := λ _ _, `[ exact ⟨_, measure_wf (λ x : Σ' {j : ℕ}, lambda (i + j + 1), x.2.sizeof₀) ⟩ ]}

def closure (i j : ℕ) (a : lambda (i + j + 1)) (b : lambda i) : lambda (i + j) :=
  closure_aux i b a

inductive beta {i} : lambda i → lambda i → Prop
  | intro : ∀ {a : lambda (i + 1)} {b : lambda i}, beta ((a.abs).app b) (closure i 0 a b)

inductive chaotic {i} : lambda i → lambda i → Prop
  | beta : ∀ {l l'}, beta l l' → chaotic l l'
  | app_left : ∀ {l l' r}, beta l l' → chaotic (l.app r) (l'.app r)
  | app_right : ∀ {l r r' : lambda i}, beta r r' → chaotic (l.app r) (l.app r')
  | abs : ∀ {body body'}, beta body body' → chaotic (body.abs) (body'.abs)

local infix `++`:50 := string.append

def append_to_string {T : Type} [has_to_string T] (a : string) (b : T) : string 
  := string.append a (has_to_string.to_string b)  


section to_string

protected def to_string_aux : ∀ {i}, lambda i → string 
| _ (var v) := "χ" ++ to_string v.val
| _ (app l r) := "(" ++ to_string_aux l ++ " " ++ to_string_aux r ++ ")"
| i (abs a) := "λχ" ++ to_string i ++ "⇒" ++ to_string_aux a ++ "."

instance : ∀ {i}, has_to_string (lambda i) := λ _, ⟨ to_string_aux ⟩

end to_string

section church

end church

end untyped
-- inductive simple_type (T : Type u) : Type u
--   | base : T → simple_type
--   | arr : simple_type → simple_type → simple_type

-- open simple_type

-- infixr `⟶`:40 := arr

-- inductive stlc 