import tactic
import data.int.basic
import data.string.basic
import init.control.alternative
universe u

section cs_algebra

end cs_algebra

section untyped

structure fresh (α : Type) : Type := (s : ℕ → α) (injective : ∀ i j, s i = s j → i = j)

def index (n : ℕ) : Type := {z : ℤ // z < n}

instance (n) : has_zero (index (n + 1)) :=
  ⟨⟨0, by {norm_num, linarith}⟩⟩

instance (n) : has_one (index (n + 2)) :=
  ⟨⟨1, by {norm_num, linarith}⟩⟩

inductive lambda : ℕ → Type
  | var {n} : index n → lambda n
  | app {n} : lambda n → lambda n → lambda n
  | abs {n} : lambda (n+1) → lambda n

infixl ` $$ `:40 := lambda.app
notation `χ`:30 i := lambda.var i
notation `ξ`:30 i `⟪ ` body ` ⟫` := @lambda.abs i body

open lambda

def lambda.sizeof₀ : ∀ {n}, lambda n → ℕ
  | _ (χ _) := 0
  | _ (l $$ r) := 1 + l.sizeof₀ + r.sizeof₀
  | i (ξ .(i) ⟪body⟫ ) := 1 + body.sizeof₀

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

def to_beta_1 {i} : lambda i → lambda i
  | (abs a $$ b) := closure i 0 a b
  | x := x

lemma to_beta_2  {i} (x : lambda i) : ∀ y, beta x y → y = to_beta_1 x :=
  begin
    intros y beta_x_y,
    induction beta_x_y,
    unfold to_beta_1,
  end

inductive chaotic : ∀ {i}, lambda i → lambda i → Prop
  | beta : ∀ {i} {l l' : lambda i}, beta l l' → chaotic l l'
  | app_left : ∀ {i} {l l' r : lambda i}, chaotic l l' → chaotic (l.app r) (l'.app r)
  | app_right : ∀ {i} {l r r' : lambda i}, chaotic r r' → chaotic (l.app r) (l.app r')
  | abs : ∀ {i} {body body' : lambda (i + 1)}, chaotic body body' → chaotic (body.abs) (body'.abs)

inductive rt_closure {α : Type*} (R : α → α → Prop) : α → α → Prop
  | refl : ∀ a, rt_closure a a
  | cons : ∀ {a c} b, R a b → rt_closure b c → rt_closure a c

@[refl]
lemma rt_closure.refl' {α : Type*} (R : α → α → Prop) (a : α) : rt_closure R a a := rt_closure.refl a

@[trans]
lemma rt_closure.trans {α} {R : α → α → Prop} {x} (y) {z} : rt_closure R x y → rt_closure R y z → rt_closure R x z :=
  begin
    intros x_y y_z,
    induction x_y, {assumption},
    refine rt_closure.cons x_y_b x_y_a_1 (x_y_ih y_z),
  end

lemma rt_closure.singleton {α : Type*} (R : α → α → Prop) (a b : α) : R a b → rt_closure R a b :=
  begin
    intro Rab,
    apply rt_closure.cons b Rab,
    refl,
  end

def rt_chaotic {i} : lambda i → lambda i → Prop := rt_closure chaotic

infix ` ~> `:50 := chaotic
infix ` ~>* `:50 := rt_chaotic

def reductions : ∀ {i} (a : lambda i), list {b // a ~> b}
  | _ (χ _) := {}
  | _ (lambda.abs body) :=
    ( do ⟨body', body_h⟩ <- reductions body,
      return ⟨body'.abs, chaotic.abs body_h⟩
    )
  | _ (l $$ r) :=
    let left_side : list {b // (l $$ r) ~> b} := 
      (do ⟨l', l_h⟩ <- reductions l, return ⟨l' $$ r, chaotic.app_left l_h ⟩ )
      in
    let right_side  : list {b // (l $$ r) ~> b} :=
      (do ⟨r', r_h⟩ <- reductions r, return ⟨l $$ r', chaotic.app_right r_h⟩ )
      in
    let beta_side : list {b // (l $$ r) ~> b}:=
      match l with
      | lambda.abs body := ( return ⟨closure _ 0 body r, chaotic.beta beta.intro⟩)
      | _ := {}
      end
      in
      beta_side.append (left_side.append right_side)

lemma in_left_append {T} (x : T) (l r : list T) : x ∈ l → x ∈ l.append r :=
  begin
    intro h,
    induction l; cases h; simp,
    {left, exact h},
    {right, exact l_ih h}
  end

lemma in_right_append {T} (x : T) (l r : list T) : x ∈ r → x ∈ l.append r :=
  begin
    intro h,
    induction l; simp,
    {exact h},
    {right, exact l_ih}
  end

lemma reductions_complete {i} {x y : lambda i} : x ~> y → y ∈ subtype.val <$> reductions x :=
  begin
    intro H,
    induction H,

    {
      induction H_a,
      unfold reductions,
      simp,
      use beta.intro,
      apply in_left_append,
      unfold reductions._match_4,
      rw list.mem_pure,
    },

    {
      unfold reductions,
      simp at *,
      split,
      apply in_right_append,
      apply in_left_append,
      rw list.mem_bind,
      use ⟨H_l', H_a⟩,
      split, {cases H_ih, apply H_ih_h},
      unfold reductions._match_2,
      rw list.mem_pure,
    },

    {
      unfold reductions,
      simp at *,
      split,
      {
      apply in_right_append,
      apply in_right_append,
      rw list.mem_bind,
      use ⟨H_r', H_a⟩,
      split, {cases H_ih, apply H_ih_h},
      unfold reductions._match_3,
      rw list.mem_pure,
      }
    },

    {
      unfold reductions,
      simp at *,
      split,
      use H_body',
      use H_a,
      split, {cases H_ih, apply H_ih_h},
      unfold reductions._match_1,
      rw list.mem_pure,
    }
  end

@[refl]
lemma rt_chaotic.refl {i} : ∀ x : lambda i, x ~>* x := λ x, rt_closure.refl' _ x 

@[trans]
lemma rt_chaotic.trans {i} {x y z : lambda i} : x ~>* y → y ~>* z → x ~>* z :=
  λ x_y y_z, rt_closure.trans y x_y y_z

def rt_chaotic_equi {i} (a b : lambda i) := ∃ c, a ~> c ∧ b ~> c

infix ` ≅ `:50 := rt_chaotic_equi

section to_string

local infix `++`:50 := string.append

protected def to_string_aux : ∀ {i}, lambda i → string 
| _ (var v) := "χ" ++ to_string v.val
| _ (app l r) := "(" ++ to_string_aux l ++ " $$ " ++ to_string_aux r ++ ")"
| i (abs a) := "λχ" ++ to_string i ++ "[" ++ to_string_aux a ++ "]"

instance : ∀ {i}, has_to_string (lambda i) := λ _, ⟨ to_string_aux ⟩

end to_string

section repr

instance {i} : has_repr (lambda i) :=
  { repr := to_string }

end repr

section church

def lambda.id : lambda 0 := (var ⟨0, by omega⟩).abs

def lambda.tt : lambda 0 := ((var ⟨0, by norm_num⟩)).abs.abs
def lambda.ff : lambda 0 := ((var ⟨1, by norm_num⟩)).abs.abs

def lambda.of_nat_aux  : ℕ → lambda 2
  | 0 := χ 0
  | (n+1) := (χ 1) $$ lambda.of_nat_aux n

@[simp] 
lemma lambda.of_nat_aux_zero : lambda.of_nat_aux 0 = @var 2 0 := rfl

@[simp] 
lemma lambda.of_nat_aux_succ {n} : lambda.of_nat_aux (n + 1) = (var 1 $$ lambda.of_nat_aux n) := rfl

def lambda.of_nat : ℕ → lambda 0 :=
  λ n, (lambda.of_nat_aux n).abs.abs

instance : has_zero (lambda 0) := ⟨lambda.of_nat 0⟩

@[simp] 
lemma lambda.of_nat_def {n} : lambda.of_nat n = ((lambda.of_nat_aux n).abs.abs) := rfl

def lambda.succ : lambda 0 :=
  let n : lambda 3 := var 0 in
  let z : lambda 3 := var 1 in
  let f : lambda 3 := var ⟨2, by norm_num⟩ in
  let body : lambda 3 := f $$ (n $$ z $$ f) in
  body.abs.abs.abs

def lambda.add : lambda 0 :=
  let n : lambda 4 := var 0 in
  let m : lambda 4 := var 1 in
  let z : lambda 4 := var ⟨2, by norm_num⟩ in
  let f : lambda 4 := var ⟨3, by norm_num⟩ in
  let body : lambda 4 := n $$ (m $$ z $$ f) $$ f in
  body.abs.abs.abs.abs

def two_plus_two := lambda.add $$ (lambda.of_nat 2) $$ (lambda.of_nat 2)

@[simp]
lemma two_plus_two_def : two_plus_two = (lambda.add $$ (lambda.of_nat 2) $$ (lambda.of_nat 2)) := rfl

def equiv_on_args : ∀ {i}, ℕ → lambda i → lambda i → Prop
  | i 0 a b := a ≅ b
  | i (n+1) a b := ∀ arg : lambda i, equiv_on_args n (a.app arg) (b.app arg)

lemma equiv_on_globals_aux (i n : ℕ) : -↑(n + 1) < (↑i : int) :=
begin
  induction n,
  {simp, linarith},
  {transitivity -(↑n_n + 1 : int), simp, linarith, exact n_ih}
end

def equiv_on_globals {i} : ℕ → lambda i → lambda i → Prop
| 0 a b := a ≅ b
| (n+1) a b := 
  let g : lambda i := var ⟨-↑(n+1), by {apply equiv_on_globals_aux}⟩ in
  equiv_on_globals n (a.app g) (b.app g)

end church

end untyped
-- inductive simple_type (T : Type u) : Type u
--   | base : T → simple_type
--   | arr : simple_type → simple_type → simple_type

-- open simple_type

-- infixr `⟶`:40 := arr

-- inductive stlc 