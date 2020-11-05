import data.vector
import tactic
import data.finset

structure FirstOrder :=
  (rels : Type) (funs : Type) (cons : Type)


structure model_in (𝕃 : FirstOrder) :=
  (A : Type)
  (A_is_inhabited : inhabited A)
  (on_rels : 𝕃.rels → A → A → Prop)
  (on_funs : 𝕃.funs → A → A → A)
  (on_cons : 𝕃.cons → A)

section

inductive term (𝕃 : FirstOrder) (T: Type) : Type
  | var : T → term  
  | func : 𝕃.funs → term → term → term
  | lit : 𝕃.cons → term

open decidable

instance term_decidable_eq (V) (𝕃 : FirstOrder) 
  [decidable_eq V] [decidable_eq 𝕃.funs] [decidable_eq 𝕃.cons] 
  : decidable_eq (term 𝕃 V) 
  | (term.var x) (term.var y) := 
    match _inst_1 x y with
    | is_true xeqy := is_true (xeqy ▸ eq.refl (term.var x))
    | is_false xney := is_false (λ h, term.no_confusion h (λ xeqy, absurd xeqy xney))
    end
  | (term.func xf xl xr) (term.func yf yl yr) :=
    match _inst_2 xf yf, term_decidable_eq xl yl, term_decidable_eq xr yr with
    | is_false fneq, _, _ := is_false (λ h, term.no_confusion h (λ feq, absurd feq fneq))
    | _, is_false lneq, _ := is_false (λ h, term.no_confusion h (λ _ leq, absurd leq lneq))
    | _, _, is_false rneq := is_false (λ h, term.no_confusion h (λ _ _ req, absurd req rneq))
    | is_true feq, is_true leq, is_true req := is_true begin clear _match, congr; assumption end
    end
  | (term.lit x) (term.lit y) := 
    match _inst_3 x y with
    | is_true xeqy := is_true (xeqy ▸ eq.refl (term.lit x))
    | is_false xney := is_false (λ h, term.no_confusion h (λ xeqy, absurd xeqy xney))
    end
  | (term.var _) (term.func _ _ _)  := is_false (λ h, term.no_confusion h)
  | (term.var _) (term.lit _)       := is_false (λ h, term.no_confusion h)
  | (term.func _ _ _) (term.var _)  := is_false (λ h, term.no_confusion h)
  | (term.func _ _ _) (term.lit _)  := is_false (λ h, term.no_confusion h)
  | (term.lit _) (term.var _)       := is_false (λ h, term.no_confusion h)
  | (term.lit _) (term.func _ _ _)  := is_false (λ h, term.no_confusion h)

def term.means_aux {V} {𝕃} (𝕌 : model_in 𝕃) (ctx : V → 𝕌.A) : term 𝕃 V → 𝕌.A 
  | (term.var v) := ctx v
  | (term.lit c) := 𝕌.on_cons c
  | (term.func f l r) := 𝕌.on_funs f (l.means_aux) (r.means_aux)

def term.means {V} {𝕃} (t : term 𝕃 V) (𝕌 : model_in 𝕃) (ctx : V → 𝕌.A) : 𝕌.A :=
  term.means_aux 𝕌 ctx t

def term.map {𝕃} {V U} : term 𝕃 V → (V → U) → term 𝕃 U
  | (term.var v) f := term.var (f v)
  | (term.lit c) _ := term.lit c
  | (term.func name l r) f := term.func name (l.map f) (r.map f)

lemma term.map_inj {𝕃 : FirstOrder} {V U : Type}
  (c : V → U)
  (p : function.injective c) :
  function.injective (λ (t : term 𝕃 V), t.map c)
  | (term.var v₁)         (term.var v₂)        h := p (term.var.inj h) ▸ eq.refl _
  | (term.lit x)          (term.lit y)         h := term.lit.inj h ▸ eq.refl _
  | (term.func xf xl xr)  (term.func yf yl yr) h := 
    let ⟨feq, leq, req⟩ := term.func.inj h in feq ▸ term.map_inj leq ▸ term.map_inj req ▸ eq.refl _
  | (term.var _) (term.func _ _ _)  h := term.no_confusion h
  | (term.var _) (term.lit _)       h := term.no_confusion h
  | (term.func _ _ _) (term.var _)  h := term.no_confusion h
  | (term.func _ _ _) (term.lit _)  h := term.no_confusion h
  | (term.lit _) (term.var _)       h := term.no_confusion h
  | (term.lit _) (term.func _ _ _)  h := term.no_confusion h

def term.map' {𝕃} {V U} : (V ↪ U) → term 𝕃 V ↪ term 𝕃 U
  | ⟨c, p⟩ := ⟨λ t, t.map c, term.map_inj c p⟩

inductive atomic_formula (𝕃 : FirstOrder) (V) : Type
  | rel : option 𝕃.rels → term 𝕃 V → term 𝕃 V → atomic_formula

def atomic_formula.map {𝕃} {V} (a : atomic_formula 𝕃 V) {U : Type} (f : V → U) : atomic_formula 𝕃 U :=
  match a with 
  | atomic_formula.rel name l r := atomic_formula.rel name (l.map f) (r.map f)
  end

lemma atomic_formula.map_inj {𝕃 : FirstOrder} {V U : Type}
  (c : V → U)
  (p : function.injective c) :
  function.injective (λ (a : atomic_formula 𝕃 V), a.map c) 
  | (atomic_formula.rel name₁ l₁ r₁) (atomic_formula.rel name₂ l₂ r₂) h :=
    let ⟨feq, leq, req⟩ := atomic_formula.rel.inj h in feq ▸ term.map_inj c p leq ▸ term.map_inj c p req ▸ eq.refl _

def atomic_formula.map' {𝕃} {V} {U : Type} : (V ↪ U) → atomic_formula 𝕃 V ↪ atomic_formula 𝕃 U
  | ⟨c, p⟩ := ⟨λ a, a.map c, atomic_formula.map_inj c p⟩

def atomic_formula.means {V} {𝕃 : FirstOrder} (a : atomic_formula 𝕃 V) (𝕌 : model_in 𝕃) (ctx : V → 𝕌.A) :
 Prop :=
 let meaning_of := λ t : term 𝕃 V, t.means 𝕌 ctx in
  match a with
  | (atomic_formula.rel ρ l r) := option.cases_on ρ eq 𝕌.on_rels (meaning_of l) (meaning_of l)
    end

instance atomic_formula.decidable_eq (V) (𝕃 : FirstOrder) 
  [decidable_eq V] [decidable_eq 𝕃.funs] [decidable_eq 𝕃.cons] [decidable_eq 𝕃.rels]
  : decidable_eq (atomic_formula 𝕃 V) 
  | (atomic_formula.rel xρ xl xr) (atomic_formula.rel yρ yl yr) := 
    if H : xρ = yρ ∧ xl = yl ∧ xr = yr
      then is_true (let ⟨ρeq, leq, req⟩ := H in ρeq ▸ leq ▸ req ▸ eq.refl (atomic_formula.rel xρ xl xr))
      else is_false (λ h, atomic_formula.no_confusion h (λ ρeq leq req, H ⟨ρeq, leq, req⟩))

inductive formula (𝕃 : FirstOrder) : ℕ → Type
  | atomic : ∀ {n}, ∀ atom : atomic_formula 𝕃 (fin n), formula n
  | and : ∀ {n}, ∀ l r : formula n, formula n
  | not :  ∀ {n}, ∀ f : formula n, formula n
  | for_all : ∀ {n}, ∀ f : formula (n+1), formula n

instance formula.decidable_eq (𝕃 : FirstOrder) 
  [decidable_eq 𝕃.funs] [decidable_eq 𝕃.cons] [decidable_eq 𝕃.rels]
  : ∀ {n}, decidable_eq (formula 𝕃 n) :=
  begin
    intros n x y,
    induction x; cases y,
    case formula.atomic formula.atomic
      { exact match atomic_formula.decidable_eq _ _ x_atom y_atom with
        | is_true x_eq_y := is_true (x_eq_y ▸ eq.refl _)
        | is_false x_neq_y := is_false $ λ h, formula.no_confusion h $ λ _ x_eq_y, x_neq_y $ eq_of_heq x_eq_y
        end,
      },
    case formula.and formula.and
    { exact match x_ih_l y_l, x_ih_r y_r with
      | is_true leq, is_true req := is_true (leq ▸ req ▸ eq.refl _)
      | is_false lneq, _ := is_false (λ h, formula.no_confusion h (λ _ leq _, lneq (eq_of_heq leq)))
      | _, is_false rneq := is_false (λ h, formula.no_confusion h (λ _ _ req, rneq (eq_of_heq req)))
      end,
    },
    case formula.not formula.not
    { exact match x_ih y_f with
      | is_true x_eq_y := is_true (x_eq_y ▸ eq.refl _)
      | is_false x_neq_y := is_false $ λ h, formula.no_confusion h $ λ _ x_eq_y, x_neq_y $ eq_of_heq x_eq_y
      end,
    },
    case formula.for_all formula.for_all
    { exact match x_ih y_f with
      | is_true x_eq_y := is_true (x_eq_y ▸ eq.refl _)
      | is_false x_neq_y := is_false $ λ h, formula.no_confusion h $ λ _ x_eq_y, x_neq_y $ eq_of_heq x_eq_y
      end
    },
    all_goals {left, intro h, exact formula.no_confusion h},
  end

def fin.lift {n} : fin n → fin (n+1)
  | ⟨x, x_lt_n⟩ := ⟨x, nat.lt.step x_lt_n⟩

def lift_formula {𝕃} : ℕ → ∀ {n : ℕ}, formula 𝕃 n → formula 𝕃 (n + 1)
  | d _ (formula.atomic a) := formula.atomic $ a.map (λ x, (if x.val ≤ d then fin.lift else fin.succ) x)
  | d _ (formula.and l r) := formula.and (lift_formula d l) (lift_formula d r)
  | d _ (formula.not f) := formula.not (lift_formula d f)
  | d _ (formula.for_all f) := formula.for_all (lift_formula (d+1) f)

def lift_formula' {𝕃} : ℕ → ∀ {n : ℕ}, formula 𝕃 n 

instance {𝕃} (n : ℕ) : has_lift (formula 𝕃 n) (formula 𝕃 (n+1)) :=
  has_lift.mk (λ f : formula 𝕃 n, lift_formula 0 f)

instance {𝕃} (n : ℕ) : has_lift (finset (formula 𝕃 n)) (finset (formula 𝕃 (n+1))) :=
  has_lift.mk 
  (λ s, finset.map 
    begin 
      existsi lift_formula 0,
      unfold function.injective,
      intros x y fx_eq_fy,
      induction x; cases y;
      unfold lift_formula at fx_eq_fy,
      simp,
    end s)

@[simp]
def sentence (𝕃 : FirstOrder) := formula 𝕃 0

def nil' {A} : fin 0 → A
  | ⟨n, p⟩ := false.rec A (nat.not_lt_zero n p)

def cons' {T} (x : T) {n} (f : fin n → T) : fin (n+1) → T
  | ⟨0, _⟩ := x
  | ⟨n+1, p⟩ := f ⟨n, (add_lt_add_iff_right 1).mp p⟩

def formula.is_true_in {𝕃 : FirstOrder} (𝕌 : model_in 𝕃) : ∀ {n}, formula 𝕃 n → (fin n → 𝕌.A) → Prop
  | _ (formula.atomic a) cxt := a.means 𝕌 cxt 
  | _ (formula.and l r) cxt := l.is_true_in cxt ∧ r.is_true_in cxt
  | _ (formula.not f) cxt := ¬ (f.is_true_in cxt)
  | _ (formula.for_all f) cxt := ∀ x : 𝕌.A, f.is_true_in (cons' x cxt)

def sentence.is_true_in {𝕃 : FirstOrder} (s : sentence 𝕃) (𝕌 : model_in 𝕃) : Prop := 
  formula.is_true_in 𝕌 s nil'

def model_in.is_model_of {𝕃 : FirstOrder} (𝕌 : model_in 𝕃) (S : set (sentence 𝕃)) : Prop :=
  ∀ s : sentence 𝕃, s ∈ S → s.is_true_in 𝕌

def set_sentence.concequence_of {𝕃} (S : set (sentence 𝕃)) (s : sentence 𝕃) :=
  ∀ 𝕌 : model_in 𝕃, 𝕌.is_model_of S → s.is_true_in 𝕌

structure sequent (𝕃: FirstOrder) (level : ℕ) : Type := (assumptions : finset (formula 𝕃 level)) (propsitions : finset (formula 𝕃 level))

infixr `∷`:60 := λ {α} [decidable_eq α] (x : α) (xs : finset α), insert x xs
infix `⊢`:50 := λ {𝕃 : FirstOrder} {n} (a b : finset (formula 𝕃 n)), (⟨a,b⟩ : sequent 𝕃 n)

inductive proof (𝕃: FirstOrder) 
  [decidable_eq 𝕃.funs] [decidable_eq 𝕃.cons] [decidable_eq 𝕃.rels]
  : ∀ n, sequent 𝕃 n → Type
| axiom_ : 
  ∀ n (A : formula 𝕃 n), 
  proof n (has_singleton.singleton A ⊢ {A})
| left_and_1 : 
  ∀ {n} (Γ Δ : finset (formula 𝕃 n)) (A B : (formula 𝕃 n)), 
  proof n (A ∷ Γ ⊢ Δ) →
  proof n (A.and B ∷ Γ ⊢ Δ)
| left_and_2 :
  ∀ {n} (Γ Δ : finset (formula 𝕃 n)) (A B : (formula 𝕃 n)), 
  proof n (B ∷ Γ ⊢ Δ) →
  proof n (A.and B ∷ Γ ⊢ Δ)
| right_and :
  ∀ {n} (Γ Δ Γ' Δ' : finset (formula 𝕃 n)) (A B : (formula 𝕃 n)),
  proof n (Γ ⊢ A ∷ Δ) →
  proof n (Γ' ⊢ B ∷ Δ') →
  proof n (Γ ∪ Γ' ⊢ A ∷ B ∷ (Δ ∪ Δ'))
| left_not :
  ∀ {n} (Γ Δ : finset (formula 𝕃 n)) (A : (formula 𝕃 n)),
  proof n (Γ ⊢ A ∷ Δ) →
  proof n (A.not ∷ Γ ⊢ Δ)
| right_not :
  ∀ {n} (Γ Δ : finset (formula 𝕃 n)) (A : (formula 𝕃 n)),
  proof n (Γ ⊢ A ∷ Δ) →
  proof n (A.not ∷ Γ ⊢ Δ)
| left_for_all :
  ∀ {n} (Γ Δ : finset (formula 𝕃 n)) (A : formula 𝕃 (n+1)),
  proof (A ∷ ↑Γ ⊢ ↑Δ) →
  proof (A.for_all ∷ Γ ⊢ Δ)
end