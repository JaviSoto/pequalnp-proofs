import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- For an AND, take pairs (0,8), (1,9), (2,12). The OR representatives encode p*14+q.
-- Each hypothesis is a search over the 23 gates after the first and uses the same boundary rows.
-- A constant, a copy, or an AND inactive on all the positive rows can be removed.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 24000000 in
theorem PEqualNP.Outside.R_meta_2276_42
    (andTail : let P : List ℕ := [130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064, 2112, 4100, 4104, 4128, 8194, 8196, 8208]
      let N : List ℕ := [127, 129, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
      ∀ p q : Fin 14, p.val * 14 + q.val ∈ [8, 23, 40] →
        ∀ T : Circuit, Monotone2 T → T.size ≤ 23 →
          (∀ r ∈ P, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
            [r.testBit p.val && r.testBit q.val]) = true) →
          (∀ r ∈ N, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
            [r.testBit p.val && r.testBit q.val]) = false) → False)
    (orTail : let P : List ℕ := [130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064, 2112, 4100, 4104, 4128, 8194, 8196, 8208]
      let N : List ℕ := [127, 129, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
      ∀ p q : Fin 14, p.val * 14 + q.val ∈ [1, 2, 7, 8, 9, 16, 17, 22, 23, 25, 32, 34, 37, 40] →
        ∀ T : Circuit, Monotone2 T → T.size ≤ 23 →
          (∀ r ∈ P, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
            [r.testBit p.val || r.testBit q.val]) = true) →
          (∀ r ∈ N, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
            [r.testBit p.val || r.testBit q.val]) = false) → False) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → x6 (0 : Fin (14 : ℕ)) = Bool.false ∨ x6 (7 : Fin (14 : ℕ)) = Bool.false → (x4.eval (List.ofFn x6) = Bool.true ↔ x2 x6)) → x4.eval (List.ofFn fun (x7 : Fin (14 : ℕ)) => Decidable.decide (x7 = (0 : Fin (14 : ℕ)) ∨ x7 = (7 : Fin (14 : ℕ)))) = Bool.false → (25 : ℕ) ≤ x4.size := by
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let baseWire (i : ℕ) : ℕ := if i < 14 then i else i - 1
  let wire (r : Option (Fin 14)) (bound i : ℕ) : ℕ :=
    if i = 14 then r.elim bound Fin.val else baseWire i
  let gate (r : Option (Fin 14)) (alwaysTrue : Bool) (bound : ℕ) (g : Gate) : Gate :=
    if alwaysTrue && decide (14 ∈ g.inputs) then
      if GateOp.rec (motive := fun _ => Bool) true false false (fun _ => false) false g.op then
        ⟨.and, (g.inputs.filter (· != 14)).map (wire r bound)⟩
      else ⟨.and, []⟩
    else ⟨g.op, g.inputs.map (wire r bound)⟩
  let Related (s : Bool) (old new : List Bool) : Prop :=
    14 ≤ new.length ∧ old.length = new.length + 1 ∧ old.getD 14 false = s ∧
      ∀ i, i ≠ 14 → old.getD i false = new.getD (baseWire i) false
  have relatedInit (x : Fin 14 → Bool) (s : Bool) :
      Related s (List.ofFn x ++ [s]) (List.ofFn x) := by
    refine ⟨by simp, by simp, by simp [List.getD_eq_getElem?_getD], ?_⟩
    intro i different
    by_cases raw : i < 14
    · rw [List.getD_append _ _ _ _ (by simpa using raw)]
      simp [baseWire, raw]
    · unfold baseWire
      rw [ite_eq_right raw]
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have relatedAppend (s v : Bool) (old new : List Bool) (rel : Related s old new) :
      Related s (old ++ [v]) (new ++ [v]) := by
    obtain ⟨rawSize, lengths, seed, values⟩ := rel
    refine ⟨by simp; omega, by simp [lengths],
      (List.getD_append _ _ _ _ (by omega)).trans seed, ?_⟩
    intro i different
    by_cases valid : i < old.length
    · have nvalid : baseWire i < new.length := by
        unfold baseWire
        split <;> omega
      rw [List.getD_append _ _ _ _ valid, List.getD_append _ _ _ _ nvalid]
      exact values i different
    · have past : old.length ≤ i := by omega
      have shift : baseWire i = i - 1 := ite_eq_right (by omega)
      rw [List.getD_append_right _ _ _ _ past, shift,
        List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      omega
  have rewiredRead (s : Bool) (old new : List Bool) (r : Option (Fin 14)) (bound : ℕ)
      (rel : Related s old new) (fits : new.length ≤ bound)
      (aliases : ∀ v, r = some v → new.getD v.val false = s)
      (falseSeed : r = none → s = false) :
      ∀ i, new.getD (wire r bound i) false = old.getD i false := by
    intro i
    by_cases equal : i = 14
    · subst i
      unfold wire
      rw [rel.2.2.1, ite_eq_left rfl]
      cases mapped : r with
      | none => rw [Option.elim, List.getD_eq_default _ _ fits, falseSeed mapped]
      | some v => exact aliases v mapped
    · unfold wire
      rw [ite_eq_right equal]
      exact (rel.2.2.2 i equal).symm
  have positiveFan (g : Gate)
      (original : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (r : Option (Fin 14)) (active : Bool) (bound : ℕ) :
      (gate r active bound g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        (gate r active bound g).inputs.length ≤ 2 := by
    unfold gate
    split
    · split
      · refine ⟨by simp, ?_⟩
        change ((g.inputs.filter (· != 14)).map (wire r bound)).length ≤ 2
        simpa using (List.length_filter_le _ _).trans original.2
      · simp
    · simpa using original
  have mappedValue (s : Bool) (old new : List Bool) (r : Option (Fin 14))
      (active : Bool) (bound : ℕ) (g : Gate) (rel : Related s old new)
      (fits : new.length ≤ bound) (aliases : ∀ v, r = some v → new.getD v.val false = s)
      (seed : r = none → s = active) (onlyConst : active = true → r = none)
      (positive : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
      (gate r active bound g).op.eval ((gate r active bound g).inputs.map fun i => new.getD i false) =
        g.op.eval (g.inputs.map fun i => old.getD i false) := by
    by_cases special : active && decide (14 ∈ g.inputs)
    · have both : active = true ∧ 14 ∈ g.inputs := by simpa using special
      obtain ⟨activeTrue, used⟩ := both
      have value : old.getD 14 false = true := rel.2.2.1.trans ((seed (onlyConst activeTrue)).trans activeTrue)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at positive
      rcases positive with tag | tag
      · simp only [gate, ite_eq_left special, tag, ite_true, List.map_map]
        change ((g.inputs.filter (· != 14)).map (fun i => new.getD (wire r bound i) false)).all id =
          (g.inputs.map fun i => old.getD i false).all id
        rw [Bool.eq_iff_iff]
        simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        constructor
        · intro h i seen
          by_cases different : i = 14
          · simpa [different] using value
          · have kept : i ∈ g.inputs.filter (· != 14) := by simp [seen, different]
            simpa only [wire, ite_eq_right different, ← rel.2.2.2 i different] using h i kept
        · intro h i kept
          have data := List.mem_filter.mp kept
          have different : i ≠ 14 := by simpa using data.2
          simpa only [wire, ite_eq_right different, ← rel.2.2.2 i different] using h i data.1
      · simp only [gate, ite_eq_left special, tag, ite_eq_right (by decide : ¬false = true)]
        change true = (g.inputs.map fun i => old.getD i false).any id
        symm
        exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨14, used, value⟩, rfl⟩
    · simp only [gate, ite_eq_right special, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i member
      have different : i = 14 → active = false := by
        intro equal
        subst i
        cases active with
        | false => rfl
        | true => exact (special (by simp [member])).elim
      by_cases eq : i = 14
      · exact rewiredRead s old new r bound rel fits aliases (fun none => (seed none).trans (different eq)) i
      · simp only [Function.comp_apply, wire, ite_eq_right eq, ← rel.2.2.2 i eq]
  have runLength (gs : List Gate) (xs : List Bool) :
      (gs.foldl step xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have preserves (gs : List Gate) (old : List Bool) (i : ℕ) (hi : i < old.length) :
      (gs.foldl step old).getD i false = old.getD i false := by
    induction gs generalizing old with
    | nil => rfl
    | cons g tail ih =>
      rw [List.foldl_cons, ih (step old g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have relatedFold (gs : List Gate) (s active : Bool) (old new : List Bool)
      (r : Option (Fin 14)) (bound : ℕ) (fits : new.length + gs.length ≤ bound)
      (initial : Related s old new) (copies : ∀ v, r = some v → new.getD v.val false = s)
      (seed : r = none → s = active) (onlyConst : active = true → r = none)
      (pos : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
      Related s (gs.foldl step old) ((gs.map (gate r active bound)).foldl step new) := by
    induction gs generalizing old new with
    | nil => exact initial
    | cons g gs ih =>
      have same := mappedValue s old new r active bound g initial (by simp at fits; omega)
        copies seed onlyConst (pos g (by simp))
      simp only [List.map_cons, List.foldl_cons]
      apply ih (step old g) (step new (gate r active bound g))
      · simp [step] at fits ⊢
        omega
      · change Related s (old ++ [_]) (new ++ [_])
        rw [same]
        exact relatedAppend s _ old new initial
      · intro v isCopy
        change (new ++ [_]).getD v.val false = s
        rw [List.getD_append _ _ _ _ (lt_of_lt_of_le v.isLt initial.1)]
        exact copies v isCopy
      · exact fun g used => pos g (by simp [used])
  let withoutSeed (r : Option (Fin 14)) (active : Bool) (T : Circuit) : Circuit :=
    let bound := 14 + T.gates.length
    ⟨T.gates.map (gate r active bound), wire r bound T.output⟩
  have withoutSeedFan (r : Option (Fin 14)) (active : Bool) (T : Circuit) (positives : Monotone2 T) :
      Monotone2 (withoutSeed r active T) := by
    intro g used
    change g ∈ T.gates.map _ at used
    obtain ⟨source, seen, rfl⟩ := List.mem_map.mp used
    exact positiveFan source (positives source seen) r active _
  have withoutSeedEval (r : Option (Fin 14)) (active : Bool) (T : Circuit)
      (positives : Monotone2 T) (x : Fin 14 → Bool)
      (onlyConst : active = true → r = none) (notConstantOutput : active = true → T.output ≠ 14) :
      (withoutSeed r active T).eval (List.ofFn x) =
        T.eval (List.ofFn x ++ [r.elim active x]) := by
    let bound := 14 + T.gates.length
    let s := r.elim active x
    let new := (T.gates.map (gate r active bound)).foldl step (List.ofFn x)
    have initial (v : Fin 14) (hv : r = some v) : (List.ofFn x).getD v.val false = s := by
      change (List.ofFn x).getD v.val false = r.elim active x
      rw [hv, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using v.isLt), List.getElem_ofFn]
      rfl
    have seed (no : r = none) : s = active := by simp [s, no]
    have rel := relatedFold T.gates s active (List.ofFn x ++ [s]) (List.ofFn x) r bound
      (by simp [bound]) (relatedInit x s) initial seed onlyConst fun g used => (positives g used).1
    have length : new.length = bound := by rw [runLength]; simp [bound]
    change new.getD (wire r bound T.output) false =
      (T.gates.foldl step (List.ofFn x ++ [s])).getD T.output false
    cases works : active with
    | false =>
      apply rewiredRead s _ new r bound rel (le_of_eq length) _ (fun no => (seed no).trans works)
      intro v hv
      rw [preserves _ _ _ (by simp)]
      exact initial v hv
    | true =>
      have no := notConstantOutput works
      unfold wire
      rw [ite_eq_right no]
      exact (rel.2.2.2 T.output no).symm
  let seedValue (g : Gate) (x : Fin 14 → Bool) : Bool :=
    g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
  let clip (i : ℕ) : Option (Fin 14) := if h : i < 14 then some ⟨i,h⟩ else none
  have inputValue (x : Fin 14 → Bool) (i : ℕ) :
      (List.ofFn x).getD i false = (clip i).elim false x := by
    by_cases raw : i < 14
    · unfold clip
      rw [dite_eq_left raw, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using raw),
        List.getElem_ofFn]
      rfl
    · unfold clip
      rw [dite_eq_right raw, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt raw)]
      rfl
  have seedShape (g : Gate) (positive : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      (short : g.inputs.length ≤ 2) :
      (∃ b, ∀ x, seedValue g x = b) ∨ (∃ v : Fin 14, ∀ x, seedValue g x = x v) ∨
      ∃ p q : Fin 14, p ≠ q ∧
        ((g.op = .and ∧ ∀ x, seedValue g x = (x p && x q)) ∨
         (g.op = .or ∧ ∀ x, seedValue g x = (x p || x q))) := by
    have tag : g.op = .and ∨ g.op = .or := by simpa using positive
    cases ops : g.inputs with
    | nil =>
      rcases tag with op | op
      · exact Or.inl ⟨true, fun x => by simp only [seedValue, ops, op]; rfl⟩
      · exact Or.inl ⟨false, fun x => by simp only [seedValue, ops, op]; rfl⟩
    | cons i rest =>
      cases rest with
      | nil =>
        have one (x : Fin 14 → Bool) : seedValue g x = (clip i).elim false x := by
          rcases tag with op | op
          · simp only [seedValue, ops, op]
            change ((List.ofFn x).getD i false && true) = _
            simpa only [Bool.and_true] using inputValue x i
          · simp only [seedValue, ops, op]
            change ((List.ofFn x).getD i false || false) = _
            simpa only [Bool.or_false] using inputValue x i
        cases val : clip i with
        | none => exact Or.inl ⟨false, fun x => by simpa only [val, Option.elim] using one x⟩
        | some v => exact Or.inr (Or.inl ⟨v, fun x => by simpa only [val, Option.elim] using one x⟩)
      | cons j rest =>
        have empty : rest = [] := by
          have bound : (i :: j :: rest).length ≤ 2 := ops ▸ short
          have n : rest.length = 0 := by simp only [List.length_cons] at bound; omega
          exact List.length_eq_zero_iff.mp n
        subst rest
        rcases tag with op | op
        · have values (x : Fin 14 → Bool) : seedValue g x = ((clip i).elim false x && (clip j).elim false x) := by
            simp only [seedValue, op, ops]
            change ((List.ofFn x).getD i false && ((List.ofFn x).getD j false && true)) = _
            rw [Bool.and_true, inputValue, inputValue]
          cases a : clip i with
          | none => exact Or.inl ⟨false, fun x => by simpa [a] using values x⟩
          | some p =>
            cases b : clip j with
            | none => exact Or.inl ⟨false, fun x => by simpa [b] using values x⟩
            | some q =>
              by_cases h : p = q
              · exact Or.inr (Or.inl ⟨p, fun x => by simpa [a,b,h] using values x⟩)
              · exact Or.inr (Or.inr ⟨p,q,h, Or.inl ⟨op, fun x => by simpa [a,b] using values x⟩⟩)
        · have values (x : Fin 14 → Bool) : seedValue g x = ((clip i).elim false x || (clip j).elim false x) := by
            simp only [seedValue, op, ops]
            change ((List.ofFn x).getD i false || ((List.ofFn x).getD j false || false)) = _
            rw [Bool.or_false, inputValue, inputValue]
          cases a : clip i with
          | none =>
            cases b : clip j with
            | none => exact Or.inl ⟨false, fun x => by simpa [a,b] using values x⟩
            | some q => exact Or.inr (Or.inl ⟨q, fun x => by simpa [a,b] using values x⟩)
          | some p =>
            cases b : clip j with
            | none => exact Or.inr (Or.inl ⟨p, fun x => by simpa [a,b] using values x⟩)
            | some q =>
              by_cases h : p = q
              · exact Or.inr (Or.inl ⟨p, fun x => by simpa [a,b,h] using values x⟩)
              · exact Or.inr (Or.inr ⟨p,q,h, Or.inr ⟨op, fun x => by simpa [a,b] using values x⟩⟩)
  let WireOrder (w z : List Bool) : Prop :=
    w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true
  have appendOrder (w z : List Bool) (a b : Bool)
      (inputs : WireOrder w z) (outputs : a = true → b = true) :
      WireOrder (w ++ [a]) (z ++ [b]) := by
    obtain ⟨length, ordered⟩ := inputs
    refine ⟨by simp [length], ?_⟩
    intro i active
    by_cases inside : i < w.length
    · rw [List.getD_append _ _ _ _ inside] at active
      rw [List.getD_append _ _ _ _ (length ▸ inside)]
      exact ordered i active
    · have past : w.length ≤ i := by omega
      rw [List.getD_append_right _ _ _ _ past] at active
      rw [List.getD_append_right _ _ _ _ (length ▸ past), ← length]
      cases eq : i - w.length with
      | zero => simp [eq] at active ⊢; exact outputs active
      | succ j => simp [eq] at active
  have foldOrder (gates : List Gate)
      (allPositive : ∀ g ∈ gates, g.op = .and ∨ g.op = .or)
      (w z : List Bool) (h : WireOrder w z) :
      WireOrder (gates.foldl step w) (gates.foldl step z) := by
    induction gates generalizing w z with
    | nil => exact h
    | cons g rest ih =>
      apply ih (fun a ha => allPositive a (by simp [ha]))
      unfold step
      apply appendOrder w z _ _ h
      rcases allPositive g (by simp) with tag | tag
      · rw [tag]
        change (g.inputs.map fun i => w.getD i false).all id = true →
          (g.inputs.map fun i => z.getD i false).all id = true
        simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        intro left i used
        exact h.2 i (left i used)
      · rw [tag]
        change (g.inputs.map fun i => w.getD i false).any id = true →
          (g.inputs.map fun i => z.getD i false).any id = true
        simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        rintro ⟨i, used, active⟩
        exact ⟨i, used, h.2 i active⟩
  have seedMonotone (T : Circuit) (mono : Monotone2 T) (xs : List Bool) (s : Bool) :
      T.eval (xs ++ [false]) = true → T.eval (xs ++ [s]) = true := by
    have init : WireOrder (xs ++ [false]) (xs ++ [s]) :=
      appendOrder xs xs false s ⟨rfl, fun _ h => h⟩ (by simp)
    have allPositive (g : Gate) (inTail : g ∈ T.gates) : g.op = .and ∨ g.op = .or := by
      simpa using (mono g inTail).1
    exact (foldOrder T.gates allPositive _ _ init).2 T.output
  have withoutSeedSize (r : Option (Fin 14)) (s : Bool) (T : Circuit) :
      (withoutSeed r s T).size = T.size := by
    change (T.gates.map (gate r s (14 + T.gates.length))).length = T.gates.length
    exact List.length_map _
  have decompose (g : Gate) (gs : List Gate) (out : ℕ) (x : Fin 14 → Bool) :
      (Circuit.mk (g :: gs) out).eval (List.ofFn x) =
        (Circuit.mk gs out).eval (List.ofFn x ++ [seedValue g x]) := rfl
  have noEmpty (P N : List ℕ) (hp : 130 ∈ P) (hl : 127 ∈ N) (hr : 16256 ∈ N)
      (out : ℕ)
      (good : ∀ r ∈ P, (Circuit.mk [] out).eval (List.ofFn fun i : Fin 14 => r.testBit i.val) = true)
      (bad : ∀ r ∈ N, (Circuit.mk [] out).eval (List.ofFn fun i : Fin 14 => r.testBit i.val) = false) :
      False := by
    by_cases raw : out < 14
    · have cover : ∀ i : Fin 14, (127 : ℕ).testBit i.val = true ∨ (16256 : ℕ).testBit i.val = true := by decide
      have clipped : clip out = some ⟨out, raw⟩ := dite_eq_left raw
      have value (r : ℕ) :
          (Circuit.mk [] out).eval (List.ofFn fun i : Fin 14 => r.testBit i.val) = r.testBit out := by
        change (List.ofFn (fun i : Fin 14 => r.testBit i.val)).getD out false = r.testBit out
        rw [inputValue, clipped]
        rfl
      rcases cover ⟨out, raw⟩ with left | right
      · rw [← value] at left
        exact Bool.noConfusion ((bad 127 hl).symm.trans left)
      · rw [← value] at right
        exact Bool.noConfusion ((bad 16256 hr).symm.trans right)
    · have failed := good 130 hp
      change (List.ofFn fun i : Fin 14 => (130 : ℕ).testBit i.val).getD out false = true at failed
      rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt raw)] at failed
      contradiction
  have normalizedSearch (P N : List ℕ) (hp : 130 ∈ P) (hl : 127 ∈ N) (hr : 16256 ∈ N)
      (nonedge : ∀ p q : Fin 14, p ≠ q → (2 ^ p.val + 2 ^ q.val) ∉ P →
        ∀ r ∈ P, (r.testBit p.val && r.testBit q.val) = false)
      (andCase : ∀ p q : Fin 14, p ≠ q → (2 ^ p.val + 2 ^ q.val) ∈ P →
        ∀ T : Circuit, Monotone2 T → T.size ≤ 23 →
          (∀ r ∈ P, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
            [r.testBit p.val && r.testBit q.val]) = true) →
          (∀ r ∈ N, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
            [r.testBit p.val && r.testBit q.val]) = false) → False)
      (orCase : ∀ p q : Fin 14, p ≠ q →
        ∀ T : Circuit, Monotone2 T → T.size ≤ 23 →
          (∀ r ∈ P, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
            [r.testBit p.val || r.testBit q.val]) = true) →
          (∀ r ∈ N, T.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val) ++
            [r.testBit p.val || r.testBit q.val]) = false) → False)
      (C : Circuit) (monotone : Monotone2 C)
      (positive : ∀ r ∈ P, C.eval (List.ofFn fun i : Fin 14 => r.testBit i.val) = true)
      (negative : ∀ r ∈ N, C.eval (List.ofFn fun i : Fin 14 => r.testBit i.val) = false) :
      25 ≤ C.size := by
    let xs (r : ℕ) := List.ofFn fun i : Fin 14 => r.testBit i.val
    by_contra! limit
    have contradictionAt (n : ℕ) : ∀ C : Circuit, C.size = n → n ≤ 24 → Monotone2 C →
        (∀ r ∈ P, C.eval (xs r) = true) → (∀ r ∈ N, C.eval (xs r) = false) → False := by
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        rintro ⟨gates, out⟩ size limit mono good bad
        cases gates with
        | nil => exact noEmpty P N hp hl hr out good bad
        | cons g gs =>
          let T : Circuit := ⟨gs, out⟩
          have tailMono : Monotone2 T := fun h seen => mono h (List.mem_cons_of_mem g seen)
          have firstMono := mono g (List.mem_cons_self ..)
          have sz : T.size + 1 = n := by
            change (g :: gs).length = n at size
            exact size
          have goodSeed (r : ℕ) (seen : r ∈ P) := (decompose g gs out _).symm.trans (good r seen)
          have badSeed (r : ℕ) (seen : r ∈ N) := (decompose g gs out _).symm.trans (bad r seen)
          have drop (r : Option (Fin 14)) (b : Bool) (constant : b = true → r = none)
              (notOut : b = true → T.output ≠ 14)
              (on : ∀ z ∈ P, T.eval (xs z ++ [r.elim b (fun i => z.testBit i.val)]) = true)
              (off : ∀ z ∈ N, T.eval (xs z ++ [r.elim b (fun i => z.testBit i.val)]) = false) : False := by
            let D := withoutSeed r b T
            have shorter : D.size < n := by rw [withoutSeedSize]; omega
            apply ih D.size shorter D rfl (by omega) (withoutSeedFan r b T tailMono)
            · intro z seen
              exact (withoutSeedEval r b T tailMono _ constant notOut).trans (on z seen)
            · intro z seen
              exact (withoutSeedEval r b T tailMono _ constant notOut).trans (off z seen)
          rcases seedShape g firstMono.1 firstMono.2 with ⟨b, equal⟩ | ⟨v, equal⟩ | ⟨a,b,diff,edge | joined⟩
          · have notOut (isTrue : b = true) : T.output ≠ 14 := by
              intro atSeed
              have fails := badSeed 127 hl
              rw [equal, isTrue] at fails
              change (gs.foldl step (xs 127 ++ [true])).getD out false = false at fails
              change out = 14 at atSeed
              rw [atSeed, preserves _ _ _ (by simp [xs]), List.getD_append_right _ _ _ _ (by simp [xs])] at fails
              simp [xs] at fails
            apply drop none b (fun _ => rfl) notOut
            · intro z seen
              simpa only [equal, Option.elim] using goodSeed z seen
            · intro z seen
              simpa only [equal, Option.elim] using badSeed z seen
          · apply drop (some v) false (by simp) (by simp)
            · intro z seen
              simpa only [equal, Option.elim] using goodSeed z seen
            · intro z seen
              simpa only [equal, Option.elim] using badSeed z seen
          · obtain ⟨_, equal⟩ := edge
            by_cases allowed : 2 ^ a.val + 2 ^ b.val ∈ P
            · apply andCase a b diff allowed T tailMono (by omega)
              · intro z seen
                simpa only [equal] using goodSeed z seen
              · intro z seen
                simpa only [equal] using badSeed z seen
            · apply drop none false (by simp) (by simp)
              · intro z seen
                simpa only [equal, Option.elim, nonedge a b diff allowed z seen] using goodSeed z seen
              · intro z seen
                cases output : T.eval (xs z ++ [false])
                · exact output
                · have forced := seedMonotone T tailMono (xs z) (seedValue g fun i => z.testBit i.val) output
                  rw [badSeed z seen] at forced
                  contradiction
          · obtain ⟨_, equal⟩ := joined
            apply orCase a b diff T tailMono (by omega)
            · intro z seen
              simpa only [equal] using goodSeed z seen
            · intro z seen
              simpa only [equal] using badSeed z seen
    exact contradictionAt C.size C rfl (by omega) monotone positive negative
  let renameWire (mapping : Fin 14 → Fin 14) (index : ℕ) : ℕ :=
    if input : index < 14 then (mapping ⟨index, input⟩).val else index
  let renameGate (mapping : Fin 14 → Fin 14) (gate : Gate) : Gate :=
    ⟨gate.op, gate.inputs.map (renameWire mapping)⟩
  let renameCircuit (mapping : Fin 14 → Fin 14) (circuit : Circuit) : Circuit :=
    ⟨circuit.gates.map (renameGate mapping), renameWire mapping circuit.output⟩
  have renameMonotone (mapping : Fin 14 → Fin 14) (circuit : Circuit) (original : Monotone2 circuit) :
      Monotone2 (renameCircuit mapping circuit) := by
    intro gate member
    change gate ∈ circuit.gates.map (renameGate mapping) at member
    obtain ⟨source, used, rfl⟩ := List.mem_map.mp member
    simpa [renameGate] using original source used
  let Relabelled (mapping : Fin 14 → Fin 14) (a b : List Bool) : Prop :=
    14 ≤ a.length ∧ a.length = b.length ∧
      ∀ index, a.getD (renameWire mapping index) false = b.getD index false
  have relabelInputs (mapping : Fin 14 → Fin 14) (x : Fin 14 → Bool) :
      Relabelled mapping (List.ofFn x) (List.ofFn (fun i => x (mapping i))) := by
    refine ⟨by simp, by simp, ?_⟩
    intro index
    by_cases raw : index < 14
    · unfold renameWire
      rw [dite_eq_left raw]
      rw [List.getD_eq_getElem _ _ (by simp),
          List.getD_eq_getElem _ _ (by simpa using raw)]
      simp only [List.getElem_ofFn]
    · have past : 14 ≤ index := by omega
      unfold renameWire
      rw [dite_eq_right raw, List.getD_eq_default _ _ (by simpa using past),
        List.getD_eq_default _ _ (by simpa using past)]
  have relabelAppend (mapping : Fin 14 → Fin 14) (a b : List Bool) (value : Bool)
      (relation : Relabelled mapping a b) :
      Relabelled mapping (a ++ [value]) (b ++ [value]) := by
    refine ⟨?_, by simp [relation.2.1], ?_⟩
    · have enough := relation.1
      simp only [List.length_append, List.length_singleton]
      omega
    intro index
    by_cases raw : index < 14
    · have renamed : renameWire mapping index < a.length := by
        simp only [renameWire, dite_eq_left raw]
        exact lt_of_lt_of_le (mapping ⟨index, raw⟩).isLt relation.1
      have inB : index < b.length := by have h := relation.2.1; have h' := relation.1; omega
      rw [List.getD_append _ _ _ _ renamed, List.getD_append _ _ _ _ inB]
      exact relation.2.2 index
    · have unchanged : renameWire mapping index = index := dite_eq_right raw
      rw [unchanged]
      by_cases inA : index < a.length
      · rw [List.getD_append _ _ _ _ inA, List.getD_append _ _ _ _ (relation.2.1 ▸ inA)]
        simpa only [unchanged] using relation.2.2 index
      · have past : a.length ≤ index := by omega
        rw [List.getD_append_right _ _ _ _ past,
          List.getD_append_right _ _ _ _ (relation.2.1 ▸ past), relation.2.1]
  let gateStep (state : List Bool) (gate : Gate) : List Bool :=
    state ++ [gate.op.eval (gate.inputs.map fun index => state.getD index false)]
  have relabelFold (mapping : Fin 14 → Fin 14) (gates : List Gate) (a b : List Bool)
      (relation : Relabelled mapping a b) :
      Relabelled mapping ((gates.map (renameGate mapping)).foldl gateStep a) (gates.foldl gateStep b) := by
    induction gates generalizing a b with
    | nil => exact relation
    | cons gate rest ih =>
      have operands :
          ((gate.inputs.map (renameWire mapping)).map fun i => a.getD i false) =
            (gate.inputs.map fun i => b.getD i false) := by
        rw [List.map_map]
        exact List.map_congr_left fun index _ => relation.2.2 index
      have next : Relabelled mapping (gateStep a (renameGate mapping gate)) (gateStep b gate) := by
        change Relabelled mapping
          (a ++ [gate.op.eval ((gate.inputs.map (renameWire mapping)).map fun i => a.getD i false)])
          (b ++ [gate.op.eval (gate.inputs.map fun i => b.getD i false)])
        rw [operands]
        exact relabelAppend mapping a b _ relation
      exact ih (gateStep a (renameGate mapping gate)) (gateStep b gate) next
  have renameSeeded (mapping : Fin 14 → Fin 14) (circuit : Circuit)
      (x : Fin 14 → Bool) (seed : Bool) :
      (renameCircuit mapping circuit).eval (List.ofFn x ++ [seed]) =
        circuit.eval (List.ofFn (fun i => x (mapping i)) ++ [seed]) := by
    have init := relabelAppend mapping _ _ seed (relabelInputs mapping x)
    exact (relabelFold mapping circuit.gates _ _ init).2.2 circuit.output
  let positives : List ℕ := [130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064, 2112, 4100, 4104, 4128, 8194, 8196, 8208]
  let negatives : List ℕ := [127, 129, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
  let andReps : List ℕ := [8, 23, 40]
  let orReps : List ℕ := [1, 2, 7, 8, 9, 16, 17, 22, 23, 25, 32, 34, 37, 40]
  let bits (r : ℕ) (i : Fin 14) : Bool := r.testBit i.val
  let group : Fin 16 → Fin 14 → Fin 14 :=
    ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
     ![0, 1, 4, 3, 2, 6, 5, 7, 10, 9, 8, 12, 11, 13],
     ![0, 1, 5, 3, 6, 2, 4, 7, 10, 13, 8, 11, 12, 9],
     ![0, 1, 6, 3, 5, 4, 2, 7, 8, 13, 10, 12, 11, 9],
     ![0, 3, 2, 1, 5, 4, 6, 7, 8, 11, 10, 9, 13, 12],
     ![0, 3, 4, 1, 6, 2, 5, 7, 10, 12, 8, 9, 13, 11],
     ![0, 3, 5, 1, 2, 6, 4, 7, 10, 11, 8, 13, 9, 12],
     ![0, 3, 6, 1, 4, 5, 2, 7, 8, 12, 10, 13, 9, 11],
     ![7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6],
     ![7, 8, 11, 10, 9, 13, 12, 0, 3, 2, 1, 5, 4, 6],
     ![7, 8, 12, 10, 13, 9, 11, 0, 3, 6, 1, 4, 5, 2],
     ![7, 8, 13, 10, 12, 11, 9, 0, 1, 6, 3, 5, 4, 2],
     ![7, 10, 9, 8, 12, 11, 13, 0, 1, 4, 3, 2, 6, 5],
     ![7, 10, 11, 8, 13, 9, 12, 0, 3, 5, 1, 2, 6, 4],
     ![7, 10, 12, 8, 9, 13, 11, 0, 3, 4, 1, 6, 2, 5],
     ![7, 10, 13, 8, 11, 12, 9, 0, 1, 5, 3, 6, 2, 4]]
  let imagePair (p q : Fin 14) (a : Fin 14 → Fin 14) (reps : List ℕ) : Prop :=
    (a p).val * 14 + (a q).val ∈ reps ∨ (a q).val * 14 + (a p).val ∈ reps
  letI imagePairDecidable (p q : Fin 14) (a : Fin 14 → Fin 14) (reps : List ℕ) :
      Decidable (imagePair p q a reps) := by
    unfold imagePair
    infer_instance
  have orOrbits : ∀ p q : Fin 14, p ≠ q → ∃ k : Fin 16, imagePair p q (group k) orReps := by
    decide
  have andOrbits : ∀ p q : Fin 14, 2^p.val + 2^q.val ∈ positives →
      ∃ k : Fin 16, imagePair p q (group k) andReps := by
    decide
  let pull (a : Fin 14 → Fin 14) (r : ℕ) : ℕ :=
    ((List.finRange 14).map fun i => if bits r (a i) then 2^i.val else 0).sum
  have closed : ∀ k : Fin 16,
      (∀ r ∈ positives, pull (group k) r ∈ positives ∧ ∀ i : Fin 14, bits (pull (group k) r) i = bits r (group k i)) ∧
      (∀ r ∈ negatives, pull (group k) r ∈ negatives ∧ ∀ i : Fin 14, bits (pull (group k) r) i = bits r (group k i)) := by
    decide +kernel
  let edges : List (ℕ × ℕ) :=
    [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),
     (3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let hit (x : Fin 14 → Bool) : Prop :=
    ∃ a b : Fin 14, (a.val,b.val) ∈ edges ∧ x a = true ∧ x b = true
  let boundary (x : Fin 14 → Bool) : Prop :=
    (hit x ∧ ∀ i, x i = true → ¬hit (Function.update x i false)) ∨
    ¬hit x ∧ ∀ i, x i = false → hit (Function.update x i true)
  letI hitDecidable (x : Fin 14 → Bool) : Decidable (hit x) := by
    unfold hit
    infer_instance
  letI boundaryDecidable (x : Fin 14 → Bool) : Decidable (boundary x) := by
    unfold boundary
    infer_instance
  have positiveRows : ∀ r ∈ positives, boundary (bits r) ∧ hit (bits r) ∧
      (bits r 0 = false ∨ bits r 7 = false) := by
    decide
  have negativeRows : ∀ r ∈ negatives, r = 129 ∨
      (boundary (bits r) ∧ ¬hit (bits r) ∧ (bits r 0 = false ∨ bits r 7 = false)) := by
    decide
  have nonedgeSeed : ∀ p q : Fin 14, p ≠ q → (2^p.val + 2^q.val) ∉ positives →
      ∀ r ∈ positives, (bits r p && bits r q) = false := by
    decide +kernel
  let tries (op : Bool → Bool → Bool) (p q : Fin 14) (T : Circuit) : Prop :=
    (∀ r ∈ positives, T.eval (List.ofFn (bits r) ++ [op (bits r p) (bits r q)]) = true) ∧
    (∀ r ∈ negatives, T.eval (List.ofFn (bits r) ++ [op (bits r p) (bits r q)]) = false)
  have transfer (op : Bool → Bool → Bool) (comm : ∀ x y, op x y = op y x)
      (reps : List ℕ)
      (counts : ∀ p q : Fin 14, p.val * 14 + q.val ∈ reps →
        ∀ T : Circuit, Monotone2 T → T.size ≤ 23 → tries op p q T → False)
      (p q : Fin 14) (symmetry : ∃ k : Fin 16, imagePair p q (group k) reps)
      (T : Circuit) (mono : Monotone2 T) (size : T.size ≤ 23) (truth : tries op p q T) : False := by
    obtain ⟨k, covers⟩ := symmetry
    let a := group k
    let D := renameCircuit a T
    have monoD := renameMonotone a T mono
    have sizeD : D.size ≤ 23 := by
      change (T.gates.map (renameGate a)).length ≤ 23
      change T.gates.length ≤ 23 at size
      simpa only [List.length_map] using size
    have identical : ∀ (M : List ℕ) (r : ℕ),
        pull a r ∈ M → (∀ i : Fin 14, bits (pull a r) i = bits r (a i)) →
        ∀ result : Bool, (∀ s ∈ M, T.eval (List.ofFn (bits s) ++ [op (bits s p) (bits s q)]) = result) →
        D.eval (List.ofFn (bits r) ++ [op (bits r (a p)) (bits r (a q))]) = result := by
      intro M r seen eq result assumes
      change (renameCircuit a T).eval _ = _
      rw [renameSeeded]
      rw [show (fun i => bits r (a i)) = bits (pull a r) from funext (fun i => (eq i).symm)]
      rw [← eq p, ← eq q]
      exact assumes _ seen
    have active : tries op (a p) (a q) D := by
      constructor
      · intro r seen
        obtain ⟨accepted, eq⟩ := (closed k).1 r seen
        exact identical positives r accepted eq true truth.1
      · intro r seen
        obtain ⟨accepted, eq⟩ := (closed k).2 r seen
        exact identical negatives r accepted eq false truth.2
    rcases covers with inOrder | reversed
    · exact counts (a p) (a q) inOrder D monoD sizeD active
    · apply counts (a q) (a p) reversed D monoD sizeD
      constructor
      · intro r seen
        rw [comm (bits r (a q)) (bits r (a p))]
        exact active.1 r seen
      · intro r seen
        rw [comm (bits r (a q)) (bits r (a p))]
        exact active.2 r seen
  change ∀ C : Circuit, Monotone2 C →
    (∀ x : Fin 14 → Bool, boundary x → (x 0 = false ∨ x 7 = false) →
      (C.eval (List.ofFn x) = true ↔ hit x)) →
    C.eval (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)) = false → 25 ≤ C.size
  intro C mono correct excluded
  have right (x : Fin 14 → Bool) : boundary x → (x 0 = false ∨ x 7 = false) →
      (C.eval (List.ofFn x) = true ↔ hit x) := correct x
  have on (r : ℕ) (seen : r ∈ positives) : C.eval (List.ofFn (bits r)) = true := by
    obtain ⟨edge, h, outside⟩ := positiveRows r seen
    exact (right _ edge outside).mpr h
  have off (r : ℕ) (seen : r ∈ negatives) : C.eval (List.ofFn (bits r)) = false := by
    rcases negativeRows r seen with rfl | ⟨edge, no, outside⟩
    · have exactRow : bits 129 = (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) := by decide +kernel
      rw [exactRow]
      exact excluded
    · cases value : C.eval (List.ofFn (bits r)) with
      | false => rfl
      | true => exact (no ((right _ edge outside).mp value)).elim
  apply normalizedSearch positives negatives (by decide) (by decide) (by decide) nonedgeSeed
      _ _ C mono on off
  · intro p q _ allowed T positive bound accepts rejects
    apply transfer (· && ·) Bool.and_comm andReps _ p q (andOrbits p q allowed) T positive bound ⟨accepts,rejects⟩
    intro u v rep D valid small allRows
    exact andTail u v rep D valid small allRows.1 allRows.2
  · intro p q diff T positive bound accepts rejects
    apply transfer (· || ·) Bool.or_comm orReps _ p q (orOrbits p q diff) T positive bound ⟨accepts,rejects⟩
    intro u v rep D valid small allRows
    exact orTail u v rep D valid small allRows.1 allRows.2
