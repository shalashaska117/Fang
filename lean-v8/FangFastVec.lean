/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Linear-time compiled code for the vector and slice operations of the pinned
   Aeneas library. The library stores a vector as a length-indexed list, and its
   conversion from a plain list recomputes the length of every tail, so one push
   costs time quadratic in the length of the vector. Each replacement below is
   proved equal to the library definition and registered with `csimp`. Code
   compiled in a module that imports this one calls the replacement; every
   definition and theorem keeps its meaning, because none of them changes. -/
module
public import Aeneas
public section

namespace FangFastVec
open Aeneas Aeneas.Std Aeneas.Data.ListN Result

universe u

/-- Append one element, carrying the length index structurally. -/
def snoc {α : Type u} : {n : Nat} → ListN α n → α → ListN α (n + 1)
  | _, .nil, x => .cons x .nil
  | _, .cons a rest, x => .cons a (snoc rest x)

/-- The element at a position, without converting to a plain list. -/
def get? {α : Type u} : {n : Nat} → ListN α n → Nat → Option α
  | _, .nil, _ => none
  | _, .cons a _, 0 => some a
  | _, .cons _ rest, index + 1 => get? rest index

/-- Replace the element at a position; out of range leaves the list unchanged. -/
def setAt {α : Type u} : {n : Nat} → ListN α n → Nat → α → ListN α n
  | _, .nil, _, _ => .nil
  | _, .cons _ rest, 0, x => .cons x rest
  | _, .cons a rest, index + 1, x => .cons a (setAt rest index x)

theorem toList_snoc {α : Type u} {n : Nat} (l : ListN α n) (x : α) :
    (snoc l x).toList = l.toList ++ [x] := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [snoc, ListN.toList, ih]

theorem get?_toList {α : Type u} {n : Nat} (l : ListN α n) (index : Nat) :
    get? l index = l.toList[index]? := by
  induction l generalizing index with
  | nil => rfl
  | cons a rest ih =>
    cases index with
    | zero => rfl
    | succ index => simp [get?, ListN.toList, ih]

theorem toList_setAt {α : Type u} {n : Nat} (l : ListN α n) (index : Nat) (x : α) :
    (setAt l index x).toList = l.toList.set index x := by
  induction l generalizing index with
  | nil => rfl
  | cons a rest ih =>
    cases index with
    | zero => rfl
    | succ index => simp [setAt, ListN.toList, ih]

theorem slice_length {α : Type u} (s : Slice α) : s.val.length = s.leng :=
  ListN_length s.list

theorem vec_length {α : Type u} (v : alloc.vec.Vec α) : v.val.length = v.slice.leng :=
  slice_length v.slice

/-! ## Vectors -/

def pushFast {α : Type u} (v : alloc.vec.Vec α) (x : α) : Result (alloc.vec.Vec α) :=
  let nlen := v.slice.leng + 1
  if h : nlen ≤ U32.max || nlen ≤ Usize.max then
    ok { slice := { leng := nlen, list := snoc v.slice.list x,
                    bound := by have := vec_length v; simp at h; scalar_tac } }
  else
    fail .maximumSizeExceeded

@[csimp] theorem push_eq_pushFast : @alloc.vec.Vec.push = @pushFast := by
  funext α v x
  unfold alloc.vec.Vec.push pushFast
  simp only [vec_length]
  split
  · congr 1
    apply alloc.vec.Vec.ext
    rw [alloc.vec.Vec.from_val, List.concat_eq_append]
    exact (toList_snoc v.slice.list x).symm
  · rfl

def lenFast {α : Type u} (v : alloc.vec.Vec α) : Usize :=
  Usize.ofNatCore v.slice.leng (by have := v.slice.bound; scalar_tac)

@[csimp] theorem len_eq_lenFast : @alloc.vec.Vec.len = @lenFast := by
  funext α v
  simp only [alloc.vec.Vec.len, lenFast, vec_length]

def derefFast {T : Type u} (v : alloc.vec.Vec T) : Slice T := v.slice

@[csimp] theorem deref_eq_derefFast : @alloc.vec.Vec.deref = @derefFast := by
  funext T v
  exact Slice.val_from v.slice _

/-! ## Slices -/

def sliceLenFast {α : Type u} (s : Slice α) : Usize :=
  Usize.ofNatCore s.leng (by have := s.bound; scalar_tac)

@[csimp] theorem slice_len_eq_sliceLenFast : @Slice.len = @sliceLenFast := by
  funext α s
  simp only [Slice.len, sliceLenFast, slice_length]

def indexUsizeFast {α : Type u} (s : Slice α) (i : Usize) : Result α :=
  match get? s.list i.val with
  | none => fail .arrayOutOfBounds
  | some x => ok x

@[csimp] theorem index_usize_eq_indexUsizeFast : @Slice.index_usize = @indexUsizeFast := by
  funext α s i
  simp only [Slice.index_usize, indexUsizeFast, get?_toList]
  rfl

def setFast {α : Type u} (s : Slice α) (i : Usize) (x : α) : Slice α :=
  { leng := s.leng, list := setAt s.list i.val x, bound := s.bound }

@[csimp] theorem set_eq_setFast : @Slice.set = @setFast := by
  funext α s i x
  apply Slice.ext
  rw [Slice.set, Slice.setAtNat, Slice.from_val]
  exact (toList_setAt s.list i.val x).symm

def indexMutUsizeFast {α : Type u} (s : Slice α) (i : Usize) : Result (α × (α → Slice α)) := do
  let x ← indexUsizeFast s i
  ok (x, setFast s i)

@[csimp] theorem index_mut_usize_eq_indexMutUsizeFast :
    @Slice.index_mut_usize = @indexMutUsizeFast := by
  funext α s i
  simp only [Slice.index_mut_usize, indexMutUsizeFast, index_usize_eq_indexUsizeFast,
    set_eq_setFast]
  rfl

/-- The library instance with the two indexing fields replaced. -/
def sliceIndexFast (T : Type u) : core.slice.index.SliceIndex Usize (Slice T) T := {
  get := core.slice.index.Usize.get
  get_mut := core.slice.index.Usize.get_mut
  get_unchecked := core.slice.index.Usize.get_unchecked
  get_unchecked_mut := core.slice.index.Usize.get_unchecked_mut
  index := fun i s => indexUsizeFast s i
  index_mut := fun i s => indexMutUsizeFast s i
}

@[csimp] theorem sliceIndex_eq_sliceIndexFast :
    @core.slice.index.SliceIndexUsizeSlice = @sliceIndexFast := by
  funext T
  unfold core.slice.index.SliceIndexUsizeSlice sliceIndexFast
  congr 1
  · funext i s
    simp only [core.slice.index.Usize.index, index_usize_eq_indexUsizeFast]
  · funext i s
    simp only [core.slice.index.Usize.index_mut, index_mut_usize_eq_indexMutUsizeFast]

/-! ## Iterators -/

def nextFast {T : Type u} (it : alloc.vec.into_iter.IntoIter T) :
    Result ((Option T) × (alloc.vec.into_iter.IntoIter T)) :=
  match it.slice with
  | { leng := _, list := .nil, bound := _ } => ok (none, it)
  | { leng := _, list := .cons hd tl, bound := bound } =>
    ok (some hd, { slice := { leng := _, list := tl, bound := by omega } })

@[csimp] theorem next_eq_nextFast :
    @alloc.vec.into_iter.IteratorIntoIter.next = @nextFast := by
  funext T it
  rcases it with ⟨⟨leng, list, bound⟩⟩
  cases list with
  | nil => rfl
  | cons hd tl =>
    simp only [alloc.vec.into_iter.IteratorIntoIter.next, nextFast]
    split
    · rename_i h
      simp [alloc.vec.Vec.val, Slice.val, ListN.toList] at h
    · rename_i hd' tl' h
      simp [alloc.vec.Vec.val, Slice.val, ListN.toList] at h
      obtain ⟨rfl, rfl⟩ := h
      congr 2
      apply alloc.vec.Vec.ext
      rw [alloc.vec.Vec.from_val]
      rfl

end FangFastVec

#print axioms FangFastVec.push_eq_pushFast
#print axioms FangFastVec.len_eq_lenFast
#print axioms FangFastVec.deref_eq_derefFast
#print axioms FangFastVec.slice_len_eq_sliceLenFast
#print axioms FangFastVec.index_usize_eq_indexUsizeFast
#print axioms FangFastVec.set_eq_setFast
#print axioms FangFastVec.index_mut_usize_eq_indexMutUsizeFast
#print axioms FangFastVec.sliceIndex_eq_sliceIndexFast
#print axioms FangFastVec.next_eq_nextFast
