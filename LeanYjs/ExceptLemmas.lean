/-!
# Reasoning about `Except` computations

Small `iff` lemmas that turn `x >>= f = Except.ok b` and friends into first-order
statements.  They are deliberately *not* global `simp` lemmas, so that existing `simp` calls keep
their behaviour; use them with `rw`/`simp only` or
`obtain ⟨a, ha, hb⟩ := Except.bind_eq_ok_iff.1 h`.
-/

namespace Except

variable {ε α β : Type}

theorem ok_bind (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

theorem error_bind (e : ε) (f : α → Except ε β) :
    (Except.error e : Except ε α) >>= f = Except.error e := rfl

theorem bind_eq_ok_iff {e : Except ε α} {f : α → Except ε β} {b : β} :
    e >>= f = Except.ok b ↔ ∃ a, e = Except.ok a ∧ f a = Except.ok b := by
  cases e <;> simp [ok_bind, error_bind]

theorem bind_eq_error_iff {e : Except ε α} {f : α → Except ε β} {err : ε} :
    e >>= f = Except.error err ↔
      e = Except.error err ∨ ∃ a, e = Except.ok a ∧ f a = Except.error err := by
  cases e <;> simp [ok_bind, error_bind]

theorem map_eq_ok_iff {f : α → β} {e : Except ε α} {b : β} :
    f <$> e = Except.ok b ↔ ∃ a, e = Except.ok a ∧ f a = b := by
  cases e <;> simp [Functor.map, Except.map]

theorem map_eq_ok_iff' {f : α → β} {e : Except ε α} {b : β} :
    Except.map f e = Except.ok b ↔ ∃ a, e = Except.ok a ∧ f a = b := by
  cases e <;> simp [Except.map]

theorem ok_of_isOk_bind {e : Except ε α} {f : α → Except ε β} {b : β}
    (h : e >>= f = Except.ok b) : ∃ a, e = Except.ok a :=
  let ⟨a, ha, _⟩ := bind_eq_ok_iff.1 h; ⟨a, ha⟩

end Except
