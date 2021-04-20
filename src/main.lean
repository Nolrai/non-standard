import control.monad.basic
import .hitchhike
import system.random
import data.string.basic

abbreviation rand (α : Type) := state std_gen α

open io.process.stdio

def get_nanoseconds :=
  do
  str <- io.cmd ⟨"date", ["+%N"], piped, piped, piped, none, []⟩,
  pure (str.to_nat)

def get_seconds :=
  do
  str <- io.cmd ⟨"date", ["+%s"], piped, piped, piped, none, []⟩,
  pure (str.to_nat)


def run_rand_io {α} (r : rand α) : io α := 
  do
  n₁ ← get_nanoseconds,
  n₂ ← get_seconds,
  pure (r.run (std_gen.mk n₁ n₂)).fst

def get_rand_nat (lo hi : ℕ) : rand ℕ :=
  do
    g ← get,
    let (n, g') := rand_nat g lo hi,
    put g',
    pure n

def get_rand_cell : rand wireworld.cell :=
    do
      n ← get_rand_nat 0 99,
      pure $
        if n < 40 then wireworld.cell.wall
        else if n < 90 then wireworld.cell.wire
        else if n < 95 then wireworld.cell.head
        else wireworld.cell.tail

example (n m k : ℕ) : n ≤ k → n * m ≤ k * m := by {intros, exact mul_le_mul_right' ᾰ m}

def get_rand_matrix {n m : ℕ} : rand (aMatrix n m wireworld.cell) :=
  do
  let start : array (n * m) unit := ⟨λ _, unit.star⟩,
  new <- start.mmap (λ _, get_rand_cell),
  pure {aMatrix. flattened := new}

def show_matrix {n m : ℕ} {α} (mx : aMatrix n m α) (f : α → string) : array n string :=
  have arr : array (n * m) α := mx.flattened,
  let new_arr : fin n → string := 
    λ ⟨ix, ix_lt_n⟩,
      have ix_m_le_ix_one_m : ix * m ≤ (ix + 1) * m := 
        mul_le_mul_right' (nat.le_succ ix) m,
      have ix_one_m_le_n_m : (ix + 1) * m ≤ n * m :=
        mul_le_mul_right' (nat.succ_le_iff.mpr ix_lt_n) m,
      let slice_row := (arr.slice (ix * m) ((ix + 1) * m) ix_m_le_ix_one_m ix_one_m_le_n_m) in
      slice_row.foldl "" (λ a s, (f a).append s) in
  (⟨new_arr⟩ : array n string)

def print_matrix {n m : ℕ} {α} (f : α → string) (mx : aMatrix n m α): io unit :=
  ((show_matrix mx f).mmap io.print_ln) >> pure unit.star

def print_time : io unit :=
  do
    let args : io.process.spawn_args := 
      { cmd := "date",
        args := [],
        stdin := io.process.stdio.null,
        stdout := io.process.stdio.inherit,
        stderr := io.process.stdio.inherit,
        cwd := none,
        env := [] 
      },
    result <- io.cmd args,
    io.print_ln result,
    return unit.star

def wireworld.cell.to_string : wireworld.cell → string 
  | wireworld.cell.wall := " "
  | wireworld.cell.wire := "X"
  | wireworld.cell.head := "H"
  | wireworld.cell.tail := "T"

def update_and_display {n m} : state_t (aMatrix (n+1) (m+1) wireworld.cell) io unit :=
  do
    state_t.lift (io.print_ln "--"),
    modify wireworld.update,
    m' <- get,
    state_t.lift $ print_matrix wireworld.cell.to_string m'

def main : io unit :=
  do
    print_time,
    [n, m, steps] <- list.map string.to_nat <$> io.cmdline_args,
    io.print_ln [n, m, steps],
    (start : aMatrix (n+1) (m+1) wireworld.cell) <- run_rand_io get_rand_matrix,
    io.print_ln "starting:",
    print_matrix wireworld.cell.to_string start,
    let loop : state_t (aMatrix (n+1) (m+1) wireworld.cell) io (list unit) 
      := sequence (list.repeat update_and_display steps),
    _ ← loop.run start,
    return unit.star