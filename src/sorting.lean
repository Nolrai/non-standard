import data.list.chain
import data.list
import .eff
import control.monad.basic
import control.monad.writer

def array.swap {size} {α} : fin size → fin size → array size α → array size α
  | i j arr := (arr.write i (arr.read j)).write j (arr.read i) 

def array.test {size} {α} [decidable_linear_order α] : fin size → fin size → array size α → bool
  | i j arr := arr.read i ≤ arr.read j

inductive sort_action (width : ℕ) : Type → Type
  | swap : fin width → fin width → sort_action unit
  | test : fin width → fin width → sort_action bool

local notation `𝕄`:50 := λ width α, state_t (array width ℚ) (writer (ℕ × ℕ)) α

def sort_action.on_prompt : ∀ {width} α (m : sort_action width α), 𝕄 width α
  | width .(unit) (sort_action.swap i j) := tell (0,1) *> (modify $ array.swap i j)
  | width .(bool) (sort_action.test i j) := tell (1,0) *> (array.test i j <$> get)

@[simp]
lemma sort_action.on_prompt.swap_def {width} {i j : fin width} : 
  sort_action.on_prompt _ (sort_action.swap i j) = tell (0,1) *> (modify $ array.swap i j) := rfl

@[simp]
lemma sort_action.on_prompt.test_def {width} {i j : fin width} : 
  sort_action.on_prompt _ (sort_action.test i j) = tell (1,0) *> (array.test i j <$> get) := rfl

abbreviation Sorting (width) := eff (sort_action width)

def id.run {α} : id α → α 
  | x := x

def run_sorting_aux {width : ℕ} (x) : array width ℚ × ℕ × ℕ :=
  match x with
  | ((unit.star, final), test_count, swap_count) := (final, test_count, swap_count)
  end

def run_sorting {width} (m : Sorting width unit) (arr : array width ℚ) : array width ℚ × ℕ × ℕ :=
 match ((state_t.run (m.run' _ sort_action.on_prompt) arr).run).run with
  | ((_, final), test_count, swap_count) := (final, test_count, swap_count)
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
  do_test j k >>= λ le, if le then do_swap j k else pure ()

abbreviation bubble_sort {width : ℕ} : Sorting width unit := fin.forM_ (λ j, fin.forM_ (test_and_swap j))

lemma bubble_sort_n_sq {n} (arr : array n ℚ) : ∃ m, m <= n ^ 2 ∧ (run_sorting bubble_sort arr).snd = (n ^ 2, m) :=
  begin
    unfold run_sorting,
    simp,
    unfold test_and_swap,
    simp,
    
  end