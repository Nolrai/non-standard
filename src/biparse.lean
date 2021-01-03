import data.buffer.parser

def buffer.slice (pos length : ℕ) {α : Type} (b : buffer α) : buffer α := (b.drop pos).take length   

structure biparse (α : Type) :=
  (encode : α → char_buffer)
  (decode : parser α)
  (decode_encode : 
    ∀ (b : char_buffer) (a : α) (pos length : ℕ), 
      b.slice pos length = encode a → decode b pos = (parse_result.done (pos + length) a))

