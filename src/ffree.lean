import data.pfun
section

universes u
parameter (F : Type u → Type u)

structure interpreter  (m : Type u → Type u) :=
  (map' : ∀ {α β} (f : α → β), m α → m β)
  (pure' : ∀ {α}, α → m α)
  (seq' : ∀ {α β : Type u}, m (α → β) → m α → m β)
  (bind' : ∀ {α β}, m α → (α → m β) → m β)
  (on_prompt : ∀ {α}, F α → m α)

parameter {F}

structure eff' (α : Type u) := 
  (run {m} (i : interpreter m) : m α)

def from_on_prompt {m : Type u → Type u} [monad m] 
  (on_prompt : ∀ α, F α → m α) : interpreter m :=
  { interpreter.
      map' := λ {α β} (f : α → β) ma, f <$> ma,
      pure' := λ {α} x, (pure x : m α),
      seq' := λ {α β : Type u} (mf : m (α → β)) (ma : m α), mf <*> ma,
      bind' := λ {α β} (ma : m α) (fm : α → m β), ma >>= fm,
      on_prompt := on_prompt
    }

@[simp]
lemma from_on_prompt.map'_def {m : Type u → Type u} [monad m] 
  (on_prompt : ∀ α, F α → m α) :
   (from_on_prompt on_prompt).map' = λ {α β} (f : α → β) ma, f <$> ma := rfl 

@[simp]
lemma from_on_prompt.pure_def {m : Type u → Type u} [monad m] 
  (on_prompt : ∀ α, F α → m α) :
   (from_on_prompt on_prompt).pure' = λ {α} a, pure a := rfl 

@[simp]
lemma from_on_prompt.seq'_def {m : Type u → Type u} [monad m] 
  (on_prompt : ∀ α, F α → m α) :
   (from_on_prompt on_prompt).seq' = λ {α β : Type u} (mf : m (α → β)) (ma : m α), mf <*> ma := rfl 

@[simp]
lemma from_on_prompt.bind'_def {m : Type u → Type u} [monad m] 
  (on_prompt : ∀ α, F α → m α) :
   (from_on_prompt on_prompt).bind' = λ {α β} (ma : m α) (fm : α → m β), ma >>= fm := rfl 

@[simp]
lemma from_on_prompt.on_prompt_def {m : Type u → Type u} [monad m] 
  (on_prompt : ∀ α, F α → m α) :
   (from_on_prompt on_prompt).on_prompt = on_prompt := rfl 

def eff'.to_monad {γ} {m : Type u → Type u} [monad m] 
  (x : eff' γ)
  (on_prompt : ∀ α, F α → m α) : m γ := 
  x.run (from_on_prompt on_prompt)

@[simp]
lemma eff'.to_monad_def {γ} {m : Type u → Type u} [monad m] 
  (x : eff' γ)
  (on_prompt : ∀ α, F α → m α) :
  x.to_monad on_prompt = x.run (from_on_prompt on_prompt) := rfl

instance eff'_monad : monad eff' := 
  { monad.
    map := λ {α β} (f : α → β) (xa : eff' α), {run := λ _ i, i.map' f (xa.run i)},
    pure := λ {α} (a : α), {run := λ _ i, i.pure' a},
    seq := λ {α β} (xf : eff' (α → β)) (xa : eff' α), {run := λ _ i, i.seq' (xf.run i) (xa.run i)},
    bind := λ {α β} (xa : eff' α) (xf : α → eff' β), {run := λ _ i, i.bind' (xa.run i) (λ a, (xf a).run i)}
  }

def to_monad_lawfully {γ} {m : Type u → Type u} [monad m] [is_lawful_monad m] 
  (x : eff' γ)
  (on_prompt : ∀ α, F α → m α) : m γ := 
  eff'.to_monad x on_prompt

@[simp]
lemma to_monad_lawfully_def {γ} {m : Type u → Type u} [monad m] [is_lawful_monad m] 
  (x : eff' γ)
  (on_prompt : ∀ α, F α → m α) : to_monad_lawfully x on_prompt = eff'.to_monad x on_prompt := rfl

def eff_r {α : Type u} (x y: eff' α) : Prop :=
  ∀ (m : Type u → Type u) [h_1:monad m] [h_2:@is_lawful_monad m h_1] (on_prompt), 
    let reduce (z : eff' α) := (@to_monad_lawfully α m h_1 h_2 z on_prompt : m α) in reduce x = reduce y

@[refl]
lemma eff_r.refl {α} : ∀ x : eff' α, eff_r x x := by {intros _ _ _ _ _ _, refl}
@[symm]
lemma eff_r.symm {α} : ∀ x y : eff' α, eff_r x y → eff_r y x
  | x y h m monad_m lawful on_prompt := by {intro reduce, symmetry, apply h}

lemma eff_r.iseqv (α : Type u) : equivalence (eff_r : eff' α → eff' α → Prop) :=
begin
  split,
  apply eff_r.refl,
  
  split,
  {
    intros x y h _ _ _ _ _, 
    symmetry, 
    apply h
  },

  {
    intros x y z xy yz _ _ _ _ _,
    transitivity (reduce y),
    apply xy,
    apply yz,
  },
end

instance eff'.setoid (α) : setoid (eff' α) :=
  {r := eff_r, iseqv := by apply eff_r.iseqv}

def eff (α : Type u) : Type (u + 1):= quotient (eff'.setoid α)

lemma eff.map_aux (α β : Type u)
  (f : α → β) :
  (has_equiv.equiv ⇒ has_equiv.equiv) (λ (x : eff' α), f <$> x)
    (λ (x : eff' α), f <$> x) :=
begin
  intros x y,
  unfold_projs,
  intros x_r_y _ _ _ _ _,
  simp,
  unfold_projs, simp,
  
end

lemma eff.seq_aux (α β : Type u) :
  (has_equiv.equiv ⇒ has_equiv.equiv ⇒ has_equiv.equiv) (has_seq.seq : eff' (α → β) → eff' α → eff' β) 
    has_seq.seq :=
begin
  intros mf mg mf_r_mg x y x_r_y,
  unfold_projs at *,
  intros _ _ _ _ _,
  have H : ∀ z, reduce z = z (@from_on_prompt m h_1 on_prompt),
    {intro z, refl},
  repeat {rw H},
  simp,
  congr,
  apply mf_r_mg _, assumption,
  apply x_r_y _, assumption,
end

def r_on_func {α β} (f g : α → eff' β) := ∀ x, f x ≈ g x

instance eff'.body_setoid (α β) : setoid (α → eff' β) := 
  {
    r := r_on_func, 
    iseqv :=
      begin
        split,
        {intros f x α monad_m lawful_m on_prompt reduce, refl},
        split,
        {intros x y x_y α β f g on_prompt reduce, symmetry, apply x_y},
        {
          intros x y z x_y y_z α β f g on_prompt reduce,
          transitivity (reduce (y α)),
          apply x_y,
          apply y_z,
        },
      end
  } 

lemma eff.bind_aux_aux (α β : Type u) (ma : eff' α) (x : α → eff' β)
  (m : Type u → Type u) [monad m] [is_lawful_monad m] (on_prompt : ∀ α, F α → m α ) : 
  to_monad_lawfully (λ (i : interpreter), i.bind' (ma i) (λ (a : α), x a i)) on_prompt 
    = let i := from_on_prompt on_prompt in i.bind' (ma i) (λ a, x a i) :=
  begin
    simp,
  end

lemma eff.bind_aux (α β : Type u) :
  (has_equiv.equiv ⇒ has_equiv.equiv ⇒ has_equiv.equiv) (has_bind.bind : eff' α → (α → eff' β) → eff' β) 
    has_bind.bind :=
begin
  intros mf mg mf_r_mg x y x_r_y,
  unfold_projs at *,
  intros _ _ _ _,
  simp,
  
end

end

def eff.join {F α} : eff F (eff α) → eff F α := quotient.map 

instance eff.monad : monad eff :=
  { monad.
    map := λ α β (f : α → β), quotient.map (λ x : eff' α, f <$> x) (eff.map_aux α β f) ,
    pure := λ α a, ⟦pure a⟧,
    seq := λ α β, quotient.map₂ has_seq.seq (by apply eff.seq_aux),
    bind := λ α β, quotient.map₂ has_bind.bind (by apply eff.bind_aux),
  } 

end