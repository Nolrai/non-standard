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

def fin.forM_ {m} [monad m] : ∀ {width}, (fin width → m unit) → m unit
  | 0 _ := pure ⋆ 
  | (_+1) f := f 0 *> fin.forM_ (f ∘ fin.succ)

@[simp]
lemma fin.forM_zero {m} [monad m] {f : fin 0 → m unit} : fin.forM_ f = pure ⋆ :=
  begin
    unfold fin.forM_,
  end

@[simp]
lemma fin.forM_succ {m} [monad m] (n : ℕ) {f : fin (n+1) → m unit} : fin.forM_ f = f 0 *> fin.forM_ (f ∘ fin.succ) :=
  begin
    unfold fin.forM_,
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

def bubble_sort {width : ℕ} : Sorting width unit := 
  fin.forM_ (λ j, fin.forM_ (λ i, if (i < j) then (test_and_swap i j) else pure ()))

lemma loop_count_aux {α β n} (x : MyM n α) (y : MyM n β) (arr) : 
        (y.run (x.run arr).fst.snd).snd = (y.run arr).snd → ((x *> y).run arr).snd = (x.run arr).snd + (y.run arr).snd :=
  begin
    intros H,
    cases x, cases y,
    unfold has_seq_right.seq_right function.const,
    simp at *, exact H
  end 

lemma loop_count_aux_nat  (n m : nat) : n.succ * m = m + n * m := 
  begin
    rw (mul_comm n.succ),
    rw (add_comm m),
    rw (mul_comm n),
    omega,
  end

lemma pure_run_run_test (n : ℕ)      (arr : array n ℚ) : ((pure ⋆ : Sorting n unit).run.run arr).snd = 0 := rfl

lemma loop_count {n size : ℕ} (f : fin size → Sorting n unit) (g : nat) 
  (f_test_eq : ∀ i arr, ((f i).run.run arr).snd = g) :
  ∀ arr, ((fin.forM_ f).run.run arr).snd = size * g :=
  begin
    induction size,
    {intros, simp, rw pure_run_run_test},
    {
      intros,
      have f_of_succ_test_eq : ∀ (i : fin size_n) (arr : array n ℚ), (((f ∘ fin.succ) i).run.run arr).snd = g,
        {intros i, apply f_test_eq},
      rw fin.forM_succ,
      rw Sorting.push_into_seq,
      rw loop_count_aux,
      {
        rw loop_count_aux_nat,
        rw ← size_ih (f ∘ fin.succ),
        {
          rw size_ih,
          {congr, apply f_test_eq},
          apply f_of_succ_test_eq,
        },
        apply f_of_succ_test_eq,
      },
      repeat {rw size_ih (f ∘ fin.succ) f_of_succ_test_eq},
    }
  end

@[simp]
lemma bubble_sort.zero : (bubble_sort : Sorting 0 unit) = pure () := rfl

lemma test_and_swap_test {n : ℕ}
  (i j : fin n)
  (arr : array n ℚ) :
  ((test_and_swap i j).run.run arr).snd = 1 :=
begin
  unfold Sorting.run test_and_swap,
  rw eff_lift_bind,
  unfold has_bind.bind,
  simp,
  unfold functor.map, simp,
  split_ifs,
  {unfold has_pure.pure, simp, unfold has_pure.pure},
  {unfold sort_action.on_prompt}
end

open_locale big_operators

open finset

lemma op_of_sum_aux (n) : image (λ i, n - i - 1) (range n) = range n :=
  begin
    ext,
    simp, split; intro H,
    obtain ⟨b, ⟨H₁, H₂⟩⟩ := H,
    rw ← H₂,
    omega,
    existsi (n - a - 1),
    split; omega,
  end

lemma range_cons : ∀ n : ℕ, (list.range n.succ) = 0 :: list.map (+1) (list.range n) :=
  by {
    intro n,
    induction n; unfold list.range list.range_core, {simp},
    have H : ∀ (n : ℕ) l, list.range_core n l = (list.range_core n list.nil) ++ l,
    {
      clear' n_n n_ih,
      intro n,
      induction n; unfold list.range list.range_core, 
      { simp },
      intros,
      rw n_ih,
      rw (n_ih [n_n]),
      rw list.append_assoc,
      congr,
    },
    rw H,
    simp_rw (H _ [n_n]),
    unfold list.range at n_ih,
    rw n_ih,
  }

lemma aux₂ (n) {α} [add_comm_monoid α] (f : ℕ → α) (g : ℕ → ℕ) (g_inj : function.injective g) : 
  ∑ (i : ℕ) in image g (range n), f i = ∑ (i : ℕ) in range n, f (g i) :=
  begin
    simp_rw finset.sum_eq_multiset_sum,
    congr' 1,
    unfold finset.range; simp,
    unfold multiset.map multiset.cons multiset.ndinsert quot.lift_on multiset.range multiset.erase_dup list.range coe
      lift_t has_lift_t.lift coe_t has_coe_t.coe coe_b has_coe.coe,
    apply congr_arg,
    have H : (list.map g (list.range_core n list.nil)).erase_dup = (list.map g (list.range_core n list.nil)),
    {
      have H : ∀ (l : list ℕ) (g : ℕ → ℕ), 
        l.erase_dup = l → 
        function.injective g → 
        (list.map g l).erase_dup = list.map g l, 
      {
        clear' f g g_inj n,
        unfold list.erase_dup,
        intros l g l_no_dup g_inj,
        rw list.pw_filter_map,
        have H : (λ (x y : ℕ), g x ≠ g y) = (λ x y, x ≠ y),
          {
            funext,
            rw ← iff_eq_eq, 
            exact 
              { mp  := λ H₁ H₂, H₁ (congr_arg g H₂),
                mpr := λ H₁ H₂, H₁ (g_inj H₂)
              },
          },
        simp_rw H,
        congr,
        transitivity, swap,
        apply l_no_dup,
        clear_except,
        induction l; unfold list.pw_filter,
        simp,
        congr; apply l_ih,
      },
      apply H,
      { 
        unfold list.erase_dup, 
        apply list.pw_filter_eq_self.mpr,
        clear_except,
        induction n,
        left,
        right,
        rw range_snoc,
      }
    }
    
  end

-- lemma op_of_sum {α} [add_comm_monoid α] (n : ℕ) (f : ℕ → α) :
--   (∑ (i : ℕ) in range n, f i) = (∑ (i : ℕ) in range n, f (n - i - 1)) :=
--   calc ∑ (i : ℕ) in range n, f i = ∑ (i : ℕ) in range n, f i : by refl
--     ... = ∑ (i : ℕ) in image (λ i, n - i - 1) (range n), f i : by {rw op_of_sum_aux n} 
--     ... = ∑ (i : ℕ) in (range n), f (n - i - 1) : by {extract_goal}
  
-- lemma sum_of_upto_n_aux {n : ℕ} : (n ^ 2 - n) = 2 * ∑ (i : ℕ) in range n, i:= 
--     calc (n ^ 2 - n) = ((n ^ 2 - n) : ℕ) : by refl
--       ... = n * (n + 1) : by {sorry}
--       ... = ∑ (i : ℕ) in range n, (i + (n - i)) : by {sorry}
--       ... = (∑ (i : ℕ) in range n, i) + (∑ (i : ℕ) in range n, (n - i - 1)) : by {sorry}
--       ... = (∑ (i : ℕ) in range n, i) + (∑ (i : ℕ) in range n, i) 
--         : by {congr' 1, have H := op_of_sum n id, simp at H, apply H}
--       ... = 2 * (∑ (i : ℕ) in range n, i) : by 
--         {symmetry, apply two_mul (∑ (i : ℕ) in range n, i)}

-- lemma sum_of_upto_n {n : ℕ} : (n ^ 2 + n) / 2 = ∑ (i : ℕ) in finset.range n, i :=
--   begin
--     rw sum_of_upto_n_aux,
--     simp,
--   end

-- lemma bubble_sort_n_sq_aux :
--   ∀ {n} (arr : array n ℚ),
--   (bubble_sort.run.run arr).snd = (n^2 - n)/2 :=
--   begin
--     intros, 
--     symmetry, transitivity (∑ (i:ℕ) in finset.range n, i), {clear arr, extract_goal}, symmetry,
--     {
      
--       apply loop_count, intros,
--       symmetry, transitivity n * 1, {symmetry, exact mul_one n}, symmetry,
--       apply loop_count, intros,
--       rename i_1 j,
--       clear arr arr_1,
--       rename arr_2 arr,
      
--     }
--   end

-- def Sorting.exec {α n} (m : Sorting n α) (arr : array n ℚ) : array n ℚ := (m.run.run arr).fst.snd

-- inductive is_permutation_of {n} (arr₁ arr₂ : array n ℚ) : Prop
--   | intro : 
--     ∀ (f g : fin n → fin n) 
--       (fg_id : ∀ i, f (g i) = i) 
--       (gf_id : ∀ i, g (f i) = i) 
--       (body : arr₁ = ⟨λ i, arr₂.data (f i)⟩),
--     is_permutation_of

-- infix ` ≈ ` := is_permutation_of

-- @[symm]
-- lemma is_permutation_of.symm {n} (x y : array n ℚ) : x ≈ y → y ≈ x :=
--   begin
--     intros xy,
--     cases xy,
--     apply is_permutation_of.intro xy_g xy_f xy_gf_id xy_fg_id,
--     obtain ⟨x⟩ := x, obtain ⟨y⟩ := y,
--     injection xy_body with xy_body_, clear xy_body, rename xy_body_ xy_body,
--     congr, simp_rw xy_body,
--     funext k,
--     congr, symmetry,
--     apply xy_fg_id,
--   end


-- @[trans]
-- lemma is_permutation_of.trans {n} (x y z : array n ℚ) : x ≈ y → y ≈ z → x ≈ z :=
--   begin
--     intros xy yz,
--     cases xy, cases yz,
--     apply is_permutation_of.intro (yz_f ∘ xy_f) (xy_g ∘ yz_g); intros,
--     { unfold function.comp, rw xy_fg_id, apply yz_fg_id},
--     { unfold function.comp, rw yz_gf_id, apply xy_gf_id},
--     cases x; cases y; cases z,
--     simp at *,
--     transitivity, {apply xy_body},
--     congr,
--     funext,
--     injections_and_clear,
--     rw h_2,
--   end

-- section

-- parameter n : ℕ

-- local notation `P` := λ {α} (m : Sorting n α), ∀ arr, is_permutation_of (m.exec arr) arr

-- lemma pure_run_run.def (n : ℕ) {α a} (arr : array n ℚ) : ((pure a : Sorting n α).run.run arr).fst.snd = arr := rfl

-- lemma Sorting.always_permutes {α} : ∀ m : Sorting n α, P m :=
--   begin
--     apply eff.induction P,
--     {
--       intros,
--       apply is_permutation_of.intro id id,
--       {intros, unfold id}, 
--       {intros, unfold id},
--       unfold Sorting.exec,
--       rw pure_run_run.def,
--       ext,
--       refl,
--     },

--     {
--       clear α,
--       intros α s arr,
--       cases s with i j i j,
--       case swap {
--         apply is_permutation_of.intro (switch_ix i j) (switch_ix i j),
--         {apply switch_ix_involution},
--         {apply switch_ix_involution},
--         {
--           unfold Sorting.exec,
--           unfold Sorting.run,
--           simp,
--           unfold array.swap
--         },
--       },

--       case test {
--         apply is_permutation_of.intro id id,
--         {intros, unfold id}, 
--         {intros, unfold id},
--         unfold Sorting.exec,
--         unfold Sorting.run,
--         simp,
--         cases arr,
--         unfold functor.map,
--         simp,
--         congr,
--       },

--     },

--     {
--       clear α,
--       intros α β ma fm ma_perm fm_perm arr,
--       unfold Sorting.exec Sorting.run at *,
--       simp at *,
--       transitivity (Sorting.exec ma arr),
--       {
--         cases ma,
--         simp at *,
--         unfold has_bind.bind at *,
--         simp at *,
--         apply fm_perm,
--       },
--       apply ma_perm,
--     }
--   end

-- def is_sorted {n} (arr : array n ℚ) : Prop := ∀ i j : fin n, i ≤ j ↔ arr.data i ≤ arr.data j

-- lemma buble_sort_sorts {n} (arr : array n ℚ) : is_sorted (bubble_sort.exec arr) :=
-- begin
--   induction n,
--   case zero {
--     unfold is_sorted,
--     intro,
--     apply fin_zero_elim,
--   },

--   case succ {
--     unfold is_sorted,

--   },

  
-- end

-- end
