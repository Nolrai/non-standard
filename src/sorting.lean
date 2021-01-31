import data.list.chain
import data.list
import .eff
import control.monad.basic
import control.monad.writer

def array.swap {size} {α} : fin size → fin size → array size α → array size α
  | i j arr := (arr.write i (arr.read j)).write j (arr.read i) 

def array.test {size} {α} [linear_order α] : fin size → fin size → array size α → bool
  | i j arr := arr.read i ≤ arr.read j

inductive sort_action (width : ℕ) : Type → Type
  | swap : fin width → fin width → sort_action unit
  | test : fin width → fin width → sort_action bool

structure count :=
  (test : ℕ) (swap : ℕ)

@[ext]
lemma count.ext {t t' s s' : ℕ} {t_eq : t = t'} {s_eq : s = s'} :
  {count . test := t, swap := s} = {test := t', swap := s'} := 
  begin
    rw [t_eq, s_eq]
  end

@[ext]
lemma count.ext_2 (y : count) : {count. test := y.test, swap := y.swap} = y := 
  begin
    cases y,
    congr,
  end

def count.add (a b : count) : count := ⟨a.test + b.test, a.swap + b.swap⟩

instance : has_add count := ⟨count.add⟩

@[simp]
theorem count.add_def (a b : count) : a + b = ⟨a.test + b.test, a.swap + b.swap⟩ := rfl

theorem count.add_assoc : ∀ (a b c : count), a + b + c = a + (b + c) :=
  begin
    intros,
    simp only [count.add_def],
    split; refine add_assoc _ _ _
  end

instance : has_zero count := ⟨⟨0,0⟩⟩

@[simp]
theorem count.zero_def : (0 : count) = ⟨0, 0⟩ := rfl

@[simp]
theorem count.zero_add (a : count) : 0 + a = a := 
  begin
    simp,
    cases a,
    split,
  end

@[simp]
theorem count.add_zero (a : count) : a + 0 = a := 
  begin
    simp,
    cases a,
    split,
  end

@[simp]
theorem count.add_comm (a b : count) : a + b = b + a := 
  begin
    simp,
    cases a,
    split; simp; apply add_comm,
  end

instance : add_comm_monoid count := 
  { 
     add_assoc := count.add_assoc,
     zero_add := count.zero_add,
     add_zero := count.add_zero,
     add_comm := count.add_comm,
     .. count.has_zero,
     .. count.has_add
  }

structure MyM (n : ℕ) α : Type :=
  (run : array n ℚ → ((α × array n ℚ) × count))

@[ext]
lemma MyM.ext {n α} (x y : array n ℚ → ((α × array n ℚ) × count)) : 
  x = y → {MyM . run := x} = {run := y} := 
  begin
    intros H,
    rw H,
  end

@[ext]
lemma MyM.ext_2 {n α} (x y : MyM n α) : (∀ arr, x.run arr = y.run arr) -> x = y  := 
  begin
    intros H,
    cases x, cases y,
    apply MyM.ext,
    funext,
    apply H,
  end

abbreviation get' {n : ℕ} : MyM n (array n ℚ) := 
  MyM.mk (λ arr, ((arr, arr), {test := 1, swap := 0})) 

abbreviation modify' {n : ℕ} (f : array n ℚ → array n ℚ) : MyM n unit :=
  MyM.mk (λ arr, (((), f arr), {test := 0, swap := 1}))

abbreviation MyM.pure {α n} (a : α ) : MyM n α :=
  ⟨λ arr, ((a, arr), 0)⟩

abbreviation MyM.bind {α β n} (ma : MyM n α) (fm : α → MyM n β) : MyM n β :=
  ⟨λ arr, 
    let step_1 := ma.run arr in 
    let step_2 := (fm step_1.fst.fst).run step_1.fst.snd in
    (step_2.fst, step_1.snd + step_2.snd)
  ⟩

abbreviation MyM.map {α β n} (f : α → β) (ma : MyM n α) : MyM n β :=
  MyM.bind ma (MyM.pure ∘ f)

abbreviation MyM.seq {α β : Type} {n} (mf : MyM n (α → β)) (ma : MyM n α) : MyM n β :=
  MyM.bind mf (λ f, MyM.map f ma)

instance {n} : monad (MyM n) :=
  { 
    map := λ α β, MyM.map,
    pure := λ α, MyM.pure,
    seq := λ α β, MyM.seq,
    bind := λ α β, MyM.bind 
  }

lemma MyM.id_map {n : ℕ} (α : Type) : ∀ (x : MyM n α), id <$> x = x :=
begin
  intro x,
  unfold_projs,
  cases x,
  simp,
  ext; simp,
end

lemma MyM.pure_bind {n : ℕ} :
  ∀ {α β : Type} (x : α) (f : α → MyM n β), pure x >>= f = f x :=
  begin
    intros,
    unfold_projs,
    simp,
    apply MyM.ext_2,
    intro,
    simp,
    ext; simp,
  end

lemma MyM.bind_assoc {n : ℕ} {α β γ} (x : MyM n α) (f : α → MyM n β) (g : β → MyM n γ) : 
  x >>= f >>= g = x >>= λ (x : α), f x >>= g :=
  begin
    unfold_projs, cases x, simp,
    ext; simp; ring,
  end

instance {n} : is_lawful_monad (MyM n) :=
  { 
    id_map := MyM.id_map,
    pure_bind := λ α β, MyM.pure_bind,
    bind_assoc := λ α β γ, MyM.bind_assoc 
  }

def sort_action.on_prompt : ∀ {width} α (m : sort_action width α), MyM width α
  | width .(unit) (sort_action.swap i j) := (modify' $ array.swap i j)
  | width .(bool) (sort_action.test i j) := (array.test i j <$> get')

@[simp]
lemma sort_action.on_prompt.swap_def {width} {i j : fin width} : 
  sort_action.on_prompt _ (sort_action.swap i j) = (modify' $ array.swap i j) := rfl

@[simp]
lemma sort_action.on_prompt.test_def {width} {i j : fin width} : 
  sort_action.on_prompt _ (sort_action.test i j) = (array.test i j <$> get') := rfl

abbreviation Sorting (width) := eff (sort_action width)

def id.run {α} : id α → α 
  | x := x

def run_sorting_aux {width : ℕ} (x) : array width ℚ × count :=
  match x with
  | ((unit.star, final), count) := (final, count)
  end

def run_sorting {width} (m : Sorting width unit) (arr : array width ℚ) : array width ℚ × count :=
 match (m.run' _ sort_action.on_prompt).run arr with
  | ((_, final), count) := (final, count)
  end

abbreviation do_swap {width} (j k : fin width) 
  : Sorting width unit := 
  eff.embed (sort_action.swap j k)

abbreviation do_test {width} (j k : fin width) 
  : Sorting width bool := 
  eff.embed (sort_action.test j k)

notation `⋆` := unit.star

def fin.forM_ {m} [monad m] : ∀ {width}, (fin width → m unit) → m unit
  | 0 _ := pure ⋆ 
  | (_+1) f := f 0 *> fin.forM_ (f ∘ fin.succ)

@[simp]
lemma eff_run_embed {α} {F m : Type → Type} [monad m] [is_lawful_monad m] 
  (s : F α) (p : ∀ α, F α → m α) : 
  eff.run' F (eff.embed s) p = p _ s :=
  rfl

@[simp]
lemma eff_lift_bind {α β F} {m} [monad m] [is_lawful_monad m] 
  (ma : eff F α) (fmb : α → eff F β) (p : ∀ α, F α → m α) :
  (ma >>= fmb).run' F p = ma.run' F p >>= (λ a:α, (fmb a).run' F p) :=
  begin
    unfold_projs,
    simp,
    unfold eff.run',
  end

@[simp]
lemma eff_lift_seq_right {α β F} {m} [monad m] [is_lawful_monad m] 
  (ma : eff F α) (mb : eff F β) (p : ∀ α, F α → m α) :
  (ma *> mb).run' F p = ma.run' F p *> mb.run' F p :=
  begin
    unfold_projs,
    simp,
    unfold eff.run',
  end

@[simp]
lemma eff_lift_forM_ {width F } {m} [monad m] [is_lawful_monad m] 
  (f : fin width → eff F unit) (p : ∀ α, F α → m α) : 
  (fin.forM_ f).run' F p = fin.forM_ (λ j, (f j).run' F p) :=
  begin
    revert f,
    induction width,
    case nat.zero {
      unfold fin.forM_,
      unfold eff.run',
      unfold_projs,
      simp,
    },
    case nat.succ {
      intro f,
      unfold fin.forM_,
      rw eff_lift_seq_right,
      congr,
      apply width_ih,
    }
  end

def test_and_swap {width} (j k : fin width) : Sorting width unit :=
  do_test j k >>= λ le, if le then pure () else do_swap j k 

@[simp]
lemma id.bind.def {α β} (m : id α) (f : α → id β) : id_bind m f = f m := rfl
@[simp]
lemma id.pure.def {α} (a : α) : (pure a : id α) = a := rfl
@[simp]
lemma id.run.def {α} (a : id α) : a.run = a := rfl 

abbreviation on_fst {α β γ} (f : α → β) (p : (α × γ)) : (β × γ) :=
  (f p.fst, p.snd)

lemma aux_aux {n} (arr : array n ℚ) (j k : fin n) : (array.test j k arr) ↔ (arr.read j ≤ arr.read k) :=
  begin
    
  end

lemma aux {n} (arr : array n ℚ) (j k : fin n) :
  (run_sorting (test_and_swap j k) arr) = 
  (let b := ((arr.read j ≤ arr.read k) : bool) in 
    (if b then arr else arr.swap j k, 1, if b then 0 else 1)) := 
      begin
        unfold run_sorting test_and_swap,
        simp,
        repeat { unfold eff.run' eff.run has_monad_lift.monad_lift writer_t.bind writer_t.tell state_t.lift function.const state_t.pure function.comp writer_t.pure id writer_t.bind state_t.bind get,
        try {unfold_projs},
        try {simp},
        },
        let τ := state_t (array n ℚ) (writer (ℕ×ℕ)),
        have H : ((pure ⋆ : τ unit).run arr).run.fst = (⋆, arr) := rfl,
        let τ_1 := writer_t (ℕ×ℕ) id,
        let α := (unit × array n ℚ),
        have H_1 : ((pure (⋆, arr) : τ_1 α).run.snd.fst : ℕ) = 1,
          {
            unfold_projs, 
            unfold writer_t.pure,
            simp,
          },
        split_ifs,
        {
          rw [H], simp, rw [H_1], unfold run_sorting._match_1,
        },
        {
          exfalso, apply h_1,
          rw aux_aux at h,
          apply h,
        },
      end

abbreviation bubble_sort {width : ℕ} : Sorting width unit := fin.forM_ (λ j, fin.forM_ (test_and_swap j))

lemma bubble_sort_n_sq {n} (arr : array n ℚ) :
  let ((m : ℕ), (m' : ℕ)) := (run_sorting bubble_sort arr).snd in 
    m = n^2 ∧ m' ≤ n^2 :=
  begin
    unfold run_sorting,
    simp,
    unfold test_and_swap,
    simp,
    
    
  end

