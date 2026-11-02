/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import TptpLexical

namespace Fang.TptpCandidate.Arity

abbrev Symbol := String × Nat
abbrev Table := List Symbol

/-- Independent incremental table construction. Call separately in each namespace. -/
def reserve (table : Table) (symbol : Symbol) : Nat × Table :=
  if symbol ∈ table then (table.idxOf symbol, table)
  else (table.length, table ++ [symbol])

def collect (table : Table) : List Symbol → Table
  | [] => table
  | head :: tail => collect (reserve table head).2 tail

def id (table : Table) (symbol : Symbol) : Nat := table.idxOf symbol

theorem reserve_existing {table : Table} {symbol : Symbol} (member : symbol ∈ table) :
    reserve table symbol = (table.idxOf symbol, table) := by simp [reserve, member]

theorem reserve_new {table : Table} {symbol : Symbol} (absent : symbol ∉ table) :
    reserve table symbol = (table.length, table ++ [symbol]) := by simp [reserve, absent]

theorem reserve_mem (table : Table) (symbol key : Symbol) :
    key ∈ (reserve table symbol).2 ↔ key ∈ table ∨ key = symbol := by
  unfold reserve
  split <;> simp_all

theorem reserve_nodup {table : Table} (unique : table.Nodup) (symbol : Symbol) :
    (reserve table symbol).2.Nodup := by
  unfold reserve
  split
  · exact unique
  · rename_i absent
    apply List.nodup_append.mpr
    refine ⟨unique, by simp, ?_⟩
    intro a member b only
    have same : b = symbol := List.mem_singleton.mp only
    subst b
    intro equal
    exact absent (equal ▸ member)

theorem reserve_id (table : Table) (symbol : Symbol) :
    (reserve table symbol).1 = (reserve table symbol).2.idxOf symbol := by
  unfold reserve
  split <;> simp_all [List.idxOf_append]

theorem reserve_preserves {table : Table} {key : Symbol} (member : key ∈ table)
    (symbol : Symbol) : (reserve table symbol).2.idxOf key = table.idxOf key := by
  unfold reserve
  split <;> simp [List.idxOf_append, member]

theorem collect_mem (table : Table) (occurrences : List Symbol) (key : Symbol) :
    key ∈ collect table occurrences ↔ key ∈ table ∨ key ∈ occurrences := by
  induction occurrences generalizing table with
  | nil => simp [collect]
  | cons symbol rest ih => simp [collect, ih, reserve_mem, or_assoc]

theorem collect_nodup (occurrences : List Symbol) {table : Table} (unique : table.Nodup) :
    (collect table occurrences).Nodup := by
  induction occurrences generalizing table with
  | nil => exact unique
  | cons symbol rest ih => exact ih (reserve_nodup unique symbol)

theorem collect_preserves (occurrences : List Symbol) {table : Table} {key : Symbol}
    (member : key ∈ table) : (collect table occurrences).idxOf key = table.idxOf key := by
  induction occurrences generalizing table with
  | nil => rfl
  | cons symbol rest ih =>
    rw [collect, ih ((reserve_mem table symbol key).mpr (Or.inl member))]
    exact reserve_preserves member symbol

theorem collect_append (table : Table) (left right : List Symbol) :
    collect table (left ++ right) = collect (collect table left) right := by
  induction left generalizing table with
  | nil => rfl
  | cons head tail ih => simpa only [List.cons_append, collect] using ih (reserve table head).2

theorem first_occurrence_id (earlier suffix : List Symbol) (symbol : Symbol)
    (first : symbol ∉ earlier) :
    id (collect [] (earlier ++ symbol :: suffix)) symbol = (collect [] earlier).length := by
  have absent : symbol ∉ collect [] earlier := by simpa only [collect_mem, List.not_mem_nil, false_or] using first
  rw [id, collect_append, collect, reserve_new absent]
  rw [collect_preserves suffix (by simp : symbol ∈ collect [] earlier ++ [symbol])]
  simp [List.idxOf_append, absent]

theorem id_bound {table : Table} {symbol : Symbol} (member : symbol ∈ table) :
    id table symbol < table.length := List.idxOf_lt_length_of_mem member

theorem id_roundtrip {table : Table} {symbol : Symbol} (member : symbol ∈ table) :
    table[id table symbol]? = some symbol := by
  rw [List.getElem?_eq_getElem (id_bound member)]
  simp only [id, List.getElem_idxOf]

theorem id_injective {table : Table} {left right : Symbol}
    (first : left ∈ table) (second : right ∈ table)
    (same : id table left = id table right) : left = right := by
  have one := id_roundtrip first
  have two := id_roundtrip second
  rw [same, two] at one
  exact (Option.some.inj one).symm

theorem original_ids_below_fresh (occurrences : List Symbol) {symbol : Symbol}
    (member : symbol ∈ occurrences) :
    id (collect [] occurrences) symbol < (collect [] occurrences).length := by
  apply id_bound
  exact (collect_mem [] occurrences symbol).mpr (Or.inr member)

end Fang.TptpCandidate.Arity
