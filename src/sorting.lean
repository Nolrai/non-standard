import data.list.chain
import data.list
import .eff
import control.monad.basic
import algebra.big_operators.ring

def switch_ix {n} (i j : fin n) := λ k, if i = k then j else if j = k then i else k
def array.swap {size} {α} (i j : fin size) (arr : array size α) : array size α :=
  ⟨λ k, arr.data (switch_ix i j k)⟩

lemma switch_ix_involution {n} (i j k : fin n) : switch_ix i j (switch_ix i j k) = k :=
  begin
    unfold switch_ix,
    split_ifs,
    {exact eq.trans (eq.symm h_1) h},
    {assumption},
    {assumption},
    refl,
  end

def array.test {size} {α} [linear_order α] : fin size → fin size → array size α → bool
  | i j arr := arr.data i ≤ arr.data j

inductive sort_action (width : ℕ) : Type → Type
  | swap : fin width → fin width → sort_action unit
  | test : fin width → fin width → sort_action bool

structure MyM (n : ℕ) α : Type :=
  (run : array n ℚ → ((α × array n ℚ) × ℕ))

def array.replaceEnd {α length} {first : fin length} : array length α → array (length - first) α → array length α
  | big small := 
  { data := 
    λ i, 
      if i_lt_first : i < first 
        then big.read i 
        else small.read 
          ⟨ i.val - first,
            by {
              unfold_coes,
              rw nat.sub_lt_sub_right_iff,
              exact i.property,
              have P_or_Q : i < first ∨ first.val ≤ i.val, 
                { rw fin.lt_def, exact lt_or_ge i.val first.val },
              apply or.resolve_left P_or_Q i_lt_first,
            }
          ⟩
  }

def MyM.drop {n α} (first : fin n) (m : MyM (n - first) α) : MyM n α :=
  MyM.mk 
    (λ big,
      let result := m.run $ big.slice first n (le_of_lt first.property) (le_refl n) in
        ⟨⟨result.1.1, big.replaceEnd result.1.2⟩, result.2⟩
    )


def MyM.exec {width α} (m : MyM width α) (arr : array width ℚ) : array width ℚ := (m.run arr).1.2

@[ext]
lemma MyM.ext {n α} (x y : array n ℚ → ((α × array n ℚ) × ℕ)) : 
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
  MyM.mk (λ arr, ((arr, arr), 1)) 

abbreviation modify' {n : ℕ} (f : array n ℚ → array n ℚ) : MyM n unit :=
  MyM.mk (λ arr, (((), f arr), 0))

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

def Sorting.run {width} {α} (m : Sorting width α) : MyM width α :=
 (m.run' _ sort_action.on_prompt)

@[simp]
lemma Sorting.push_into_seq {width} {α} (ma : Sorting width α) {β} (mb : Sorting width β) :
  (ma *> mb).run = (ma.run) *> mb.run :=
  begin
    cases ma,
    cases mb,
    unfold Sorting.run, simp, 
    unfold has_seq_right.seq_right, simp,
    unfold has_seq_right.seq_right,
  end

abbreviation do_swap {width} (j k : fin width) 
  : Sorting width unit := 
  eff.embed (sort_action.swap j k)

abbreviation do_test {width} (j k : fin width) 
  : Sorting width bool := 
  eff.embed (sort_action.test j k)

notation `⋆` := unit.star

def list_out : ∀ {n}, list (fin n)
  | 0 := []
  | (_ +1) := 0 :: (fin.succ <$> list_out) 

def fin.forM_ {n} {m} [monad m] (f : fin n → m unit) : m unit :=
  list.foldr (*>) (pure ⋆) (list.map f (list_out : list (fin n)))

@[simp]
lemma fin.forM_zero {m} [monad m] {f : fin 0 → m unit} : fin.forM_ f = pure ⋆ :=
  begin
    unfold fin.forM_ list_out,
    rw list.map_nil,
    rw list.foldr_nil,
  end



@[simp]
lemma fin.forM_succ {m} [monad m] (n : ℕ) {f : fin (n+1) → m unit} : 
  fin.forM_ f = f 0 *> fin.forM_ (f ∘ fin.succ) :=
  begin
    unfold fin.forM_ list_out,
    rw [list.map_cons, list.foldr_cons],
    congr' 2,
    refine list.map_map f fin.succ _,
  end

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
  end

@[simp]
lemma eff_lift_seq_right {α β F} {m} [monad m] [is_lawful_monad m] 
  (ma : eff F α) (mb : eff F β) (p : ∀ α, F α → m α) :
  (ma *> mb).run' F p = ma.run' F p *> mb.run' F p :=
  begin
    unfold_projs,
    simp,
  end

@[simp]
lemma eff_lift_pure {F m : Type → Type} (p : ∀ α : Type, F α → m α) [monad m] [is_lawful_monad m] : 
  eff.run' F (pure ⋆) p = (pure ⋆ : m unit) := rfl

@[simp]
lemma eff_lift_forM_ {width F } {m} [monad m] [is_lawful_monad m] 
  (f : fin width → eff F unit) (p : ∀ α, F α → m α) : 
  (fin.forM_ f).run' F p = fin.forM_ (λ j, (f j).run' F p) :=
  begin
    revert f,
    induction width,
    case nat.zero {
      intros f,
      simp,
    },
    case nat.succ {
      intro f,
      simp,
      congr,
      unfold eff.run' at width_ih,
      transitivity (fin.forM_ (f ∘ fin.succ)).run (mk_interpreter F p), {congr},
      rw width_ih,
      congr' 1,
    }
  end

def test_and_swap {width} (j k : fin width) : Sorting width unit :=
  do_test j k >>= λ le, if le then pure () else do_swap j k 

lemma bind_unchanged {width α β} {m : Sorting width α} {fm : α → Sorting width β} :
  ∀ i, 
  (∀ arr, (m.run.exec arr).read i = arr.read i) → 
  (∀ arr (x : α), ((fm x).run.exec arr).read i = arr.read i) →
  (∀ arr, ((m >>= fm).run.exec arr).read i = arr.read i) := 
  begin
    intros i m_unchanged fm_unchanged arr,
    let a := (m.run.run arr).1.1,
    let arr2 := (m.run.run arr).1.2,
    transitivity ((fm a).run.exec arr2).read i, {congr' 1}, 
    {transitivity (arr2.read i), apply fm_unchanged, apply m_unchanged},
  end

lemma right_seq_unchanged {width α} {m : Sorting width unit} {m₁ : Sorting width α} :
  ∀ i, 
  (∀ arr, (m.run.exec arr).read i = arr.read i) → 
  (∀ arr, (m₁.run.exec arr).read i = arr.read i) →
  (∀ arr, ((m *> m₁).run.exec arr).read i = arr.read i) := 
  begin
    intros i m_unchanged m₁_unchanged arr,
    let arr2 := (m.run.run arr).1.2,
    transitivity (m₁.run.exec arr2).read i, {congr' 1},
    {transitivity (arr2.read i), apply m₁_unchanged, apply m_unchanged},
  end

lemma do_test_unchanged {width} {j k : fin width} :
  ∀ i (arr : array width ℚ), ((do_test j k).run.exec arr).read i = arr.read i :=
  begin
    intros,
    unfold Sorting.run eff.run' MyM.exec MyM.run mk_interpreter,
    simp,
    unfold_projs,
    refl,
  end

lemma pure_unchanged {width} {α} {x : α} :
  ∀ i (arr : array width ℚ), 
  ((pure x : Sorting width α).run.exec arr).read i = arr.read i :=
  begin
    intros,
    unfold Sorting.run eff.run' MyM.exec MyM.run mk_interpreter,
  end

lemma do_swap_unchanged {width} {j k : fin width} :
  ∀ i, i ≠ j → i ≠ k → 
  ∀ (arr : array width ℚ), ((do_swap j k).run.exec arr).read i = arr.read i :=
  begin
    intros _ i_ne_j i_ne_k arr,
    unfold Sorting.run eff.run' MyM.exec MyM.run mk_interpreter,
    simp,
    unfold array.swap array.read d_array.read,
    simp,
    congr,
    unfold switch_ix,
    rw if_neg,
    rw if_neg,
    all_goals {intro H}, 
    {apply i_ne_k, symmetry, exact H},
    {apply i_ne_j, symmetry, exact H},
  end

lemma test_and_swap.unchanged {width} (j k : fin width) (arr : array width ℚ) :
  ∀ i, i ≠ j → i ≠ k → ((test_and_swap j k).run.exec arr).read i = arr.read i :=
  begin
    intros i i_ne_j i_ne_k,
    unfold test_and_swap,
    apply bind_unchanged,
    {apply do_test_unchanged},
    {
      intros arr b,
      split_ifs,
      {apply pure_unchanged},
      {apply do_swap_unchanged i i_ne_j i_ne_k},
    },
  end

def fin.trans {w : ℕ} {j : fin w} (k : fin ↑j) : fin w := 
  ⟨k.val, has_lt.lt.trans k.prop j.prop⟩

def find_max {width : ℕ} (j : fin width) : Sorting width unit :=
  fin.forM_ (λ k : fin j.val, test_and_swap (fin.trans k) j)

def find_max_unchanged {width} (j : fin width) :
  ∀ (i : fin width) (arr : array width ℚ), 
    i > j → 
    ((find_max j).run.exec arr).read i = arr.read i :=
  begin
    cases j,
    unfold find_max,
  end

def bubble_sort {width : ℕ} : Sorting width unit := 
  fin.forM_ find_max

