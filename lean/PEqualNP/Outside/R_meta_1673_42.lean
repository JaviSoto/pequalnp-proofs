import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The accepted bound for a leading AND transfers to all circuits by adding an unused AND.
-- In a circuit ending in NOT, with at most one earlier NOT, that earlier NOT's input
-- already computes the target. If there is no earlier NOT, the output is antitone.
theorem PEqualNP.Outside.R_meta_1673_42
    (andLower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (remaining : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) →
      C.size = 15 →
      C.output + 1 = 9 + C.size →
      ¬ (C.gates.getLast?.map (fun g => g.op) = some .not ∧
        C.gates.countP (fun g =>
          GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) ≤ 2) →
      False) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let read (w : List Bool) (inputs : List ℕ) : Bool :=
    (inputs.map fun i => w.getD i false).headD false
  let WireOrder (w z : List Bool) : Prop :=
    w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true
  let InputOrder (x y : Fin 9 → Bool) : Prop := ∀ i, x i = true → y i = true
  let Positive (g : Gate) : Prop := g.op = .and ∨ g.op = .or
  have rawOrder (x y : Fin 9 → Bool) (h : InputOrder x y) :
      WireOrder (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i active
    by_cases input : i < 9
    · have hx : i < (List.ofFn x).length := by simpa
      have hy : i < (List.ofFn y).length := by simpa
      rw [List.getD_eq_getElem _ _ hx, List.getElem_ofFn] at active
      rw [List.getD_eq_getElem _ _ hy, List.getElem_ofFn]
      exact h ⟨i,input⟩ active
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt input)] at active
      contradiction
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
  have foldOrder (gates : List Gate) (allPositive : ∀ g ∈ gates, Positive g)
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
  have readOrder (w z : List Bool) (inputs : List ℕ) (h : WireOrder w z) :
      read w inputs = true → read z inputs = true := by
    cases inputs with
    | nil => simp [read]
    | cons i rest => exact h.2 i
  have wiresLength (gates : List Gate) (w : List Bool) :
      (gates.foldl step w).length = w.length + gates.length := by
    induction gates generalizing w with
    | nil => simp
    | cons g rest ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have complementAtEnd (f : (Fin 9 → Bool) → Bool)
      (pre mid : List Gate) (a b : List ℕ)
      (evaluates : circuitFun 9
        ⟨pre ++ ⟨.not,a⟩ :: (mid ++ [⟨.not,b⟩]), 10 + pre.length + mid.length⟩ = f)
      (x : Fin 9 → Bool) :
      f x = !(read (mid.foldl step
        ((pre.foldl step (List.ofFn x)) ++ [!(read (pre.foldl step (List.ofFn x)) a)])) b) := by
    let w := pre.foldl step (List.ofFn x)
    let z := mid.foldl step (w ++ [!(read w a)])
    have wlen : w.length = 9 + pre.length := by simp [w, wiresLength]
    have zlen : z.length = 10 + pre.length + mid.length := by
      simp [z, wiresLength, wlen]
      omega
    have correct := congrFun evaluates x
    change ((pre ++ Gate.mk .not a :: (mid ++ [Gate.mk .not b])).foldl step
      (List.ofFn x)).getD (10 + pre.length + mid.length) false = f x at correct
    rw [List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at correct
    change (z ++ [!(read z b)]).getD (10 + pre.length + mid.length) false = f x at correct
    rw [← zlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self] at correct
    exact correct.symm
  have internalSourceIsTarget (f : (Fin 9 → Bool) → Bool)
      (low : f (fun _ => false) = false) (high : f (fun _ => true) = true)
      (pre mid : List Gate) (a b : List ℕ)
      (prePositive : ∀ g ∈ pre, Positive g) (midPositive : ∀ g ∈ mid, Positive g)
      (evaluates : circuitFun 9
        ⟨pre ++ ⟨.not,a⟩ :: (mid ++ [⟨.not,b⟩]), 10 + pre.length + mid.length⟩ = f) :
      ∀ x, read (pre.foldl step (List.ofFn x)) a = f x := by
    let u := fun x : Fin 9 → Bool => read (pre.foldl step (List.ofFn x)) a
    let w := fun x : Fin 9 → Bool =>
      read (mid.foldl step ((pre.foldl step (List.ofFn x)) ++ [!(u x)])) b
    have fEq (x : Fin 9 → Bool) : f x = !(w x) := complementAtEnd f pre mid a b evaluates x
    have uOrder {x y} (xy : InputOrder x y) :
        u x = true → u y = true :=
      readOrder _ _ a (foldOrder pre prePositive _ _ (rawOrder x y xy))
    have noCross {x y} (xy : InputOrder x y) (same : u x = u y)
        (before : f x = false) (after : f y = true) : False := by
      have internal := foldOrder pre prePositive _ _ (rawOrder x y xy)
      have appended := appendOrder _ _ (!(u x)) (!(u y)) internal (by simp [same])
      have compared := foldOrder mid midPositive _ _ appended
      have implies : w x = true → w y = true := readOrder _ _ b compared
      rw [fEq] at before after
      cases wx : w x <;> cases wy : w y <;> simp_all
    intro x
    change u x = f x
    cases hu : u x <;> cases hf : f x
    · rfl
    · have bottom : u (fun _ => false) = false := by
        cases eq : u (fun _ => false)
        · rfl
        · have impossible := uOrder (x := fun _ => false) (y := x) (by intro i; simp) eq
          simp [hu] at impossible
      exact (noCross (x := fun _ => false) (y := x) (by intro i; simp) (by rw [bottom, hu]) low hf).elim
    · have top := uOrder (x := x) (y := fun _ => true) (by intro i; simp) hu
      exact (noCross (x := x) (y := fun _ => true) (by intro i; simp) (by rw [top, hu]) hf high).elim
    · rfl
  have extractTwoNots (f : (Fin 9 → Bool) → Bool)
      (low : f (fun _ => false) = false) (high : f (fun _ => true) = true)
      (pre mid : List Gate) (a b : List ℕ)
      (preFan : FanInTwo ⟨pre,0⟩) (prePositive : ∀ g ∈ pre, Positive g)
      (midPositive : ∀ g ∈ mid, Positive g) (small : pre.length + mid.length ≤ 13)
      (computes : circuitFun 9
        ⟨pre ++ ⟨.not,a⟩ :: (mid ++ [⟨.not,b⟩]), 10 + pre.length + mid.length⟩ = f) :
      HasCircuitSize 9 f 13 := by
    let shorter : Circuit := ⟨pre, a.headD (9 + pre.length)⟩
    have computesShorter : circuitFun 9 shorter = f := by
      funext x
      have value := internalSourceIsTarget f low high pre mid a b prePositive midPositive computes x
      change (pre.foldl step (List.ofFn x)).getD (a.headD (9 + pre.length)) false = f x
      cases a with
      | nil =>
        rw [List.headD_nil, List.getD_eq_default _ _ (by simp [wiresLength])]
        simpa [read] using value
      | cons i rest => exact value
    exact ⟨shorter, preFan, by change pre.length ≤ 13; omega, fun x => congrFun computesShorter x⟩
  have oneNotImpossible (f : (Fin 9 → Bool) → Bool)
      (low : f (fun _ => false) = false) (high : f (fun _ => true) = true)
      (prior : List Gate) (inputs : List ℕ) (positive : ∀ g ∈ prior, Positive g)
      (computes : circuitFun 9 ⟨prior ++ [⟨.not,inputs⟩], 9 + prior.length⟩ = f) : False := by
    let w := fun x : Fin 9 → Bool => prior.foldl step (List.ofFn x)
    have values (x : Fin 9 → Bool) : f x = !(read (w x) inputs) := by
      have correct := congrFun computes x
      change ((prior ++ [Gate.mk .not inputs]).foldl step (List.ofFn x)).getD
        (9 + prior.length) false = f x at correct
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at correct
      change (w x ++ [!(read (w x) inputs)]).getD (9 + prior.length) false = f x at correct
      have len : (w x).length = 9 + prior.length := by simp [w, wiresLength]
      rw [← len, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self] at correct
      exact correct.symm
    have order := foldOrder prior positive _ _ (rawOrder (fun _ => false) (fun _ => true) (by intro i; simp))
    have same := readOrder _ _ inputs order
    have lo := values (fun _ => false)
    have hi := values (fun _ => true)
    rw [low] at lo
    rw [high] at hi
    change read (w (fun _ => false)) inputs = true →
      read (w (fun _ => true)) inputs = true at same
    cases zero : read (w (fun _ => false)) inputs with
    | false => simp [zero] at lo
    | true => simp [same zero] at hi
  let isNot (g : Gate) : Bool :=
    GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op
  have positiveFromFan (g : Gate) (basis :
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (notNeg : g.op ≠ .not) :
      Positive g := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at basis
    rcases basis with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (notNeg c).elim
  have extract (f : (Fin 9 → Bool) → Bool)
      (low : f (fun _ => false) = false) (high : f (fun _ => true) = true)
      (c : Circuit) (fanin : FanInTwo c) (computes : circuitFun 9 c = f)
      (small : c.size ≤ 15) (last : c.gates.getLast?.map (fun g => g.op) = some .not)
      (outputLast : c.output + 1 = 9 + c.size) (few : c.gates.countP isNot ≤ 2) :
      HasCircuitSize 9 f 13 := by
    cases tail : c.gates.getLast? with
    | none => simp [tail] at last
    | some g =>
      obtain ⟨prior, layers⟩ := List.getLast?_eq_some_iff.mp tail
      have tag : g.op = .not := by simpa [tail] using last
      rcases g with ⟨op, b⟩
      change op = .not at tag
      subst op
      have equal : c = ⟨prior ++ [⟨.not,b⟩], 9 + prior.length⟩ := by
        cases c with
        | mk gates output =>
          change gates = prior ++ [⟨.not,b⟩] at layers
          subst gates
          change output + 1 = 9 + (prior ++ [Gate.mk .not b]).length at outputLast
          simp at outputLast
          congr
          omega
      have priorFan (gate : Gate) (used : gate ∈ prior) :=
        fanin gate (by rw [layers]; exact List.mem_append_left _ used)
      have priorLimit : prior.countP isNot ≤ 1 := by
        rw [layers] at few
        simp [isNot, List.countP_append] at few
        omega
      by_cases found : ∃ gate ∈ prior, gate.op = .not
      · obtain ⟨inner, seen, innerTag⟩ := found
        obtain ⟨pre, mid, split⟩ := List.append_of_mem seen
        rcases inner with ⟨innerOp,a⟩
        change innerOp = .not at innerTag
        subst innerOp
        have zero : pre.countP isNot = 0 ∧ mid.countP isNot = 0 := by
          rw [split] at priorLimit
          have isNeg : isNot (Gate.mk .not a) = true := rfl
          simp only [List.countP_append, List.countP_cons, isNeg, ite_true] at priorLimit
          omega
        have preFan : FanInTwo ⟨pre,0⟩ := by
          intro gate member
          exact priorFan gate (by rw [split]; exact List.mem_append_left _ member)
        have prePos (gate : Gate) (used : gate ∈ pre) : Positive gate := by
          have no := List.countP_eq_zero.mp zero.1 gate used
          exact positiveFromFan gate (preFan gate used).1 (by intro nt; simp [isNot, nt] at no)
        have midPos (gate : Gate) (used : gate ∈ mid) : Positive gate := by
          have no := List.countP_eq_zero.mp zero.2 gate used
          have member : gate ∈ prior := by rw [split]; simp [used]
          exact positiveFromFan gate (priorFan gate member).1 (by intro nt; simp [isNot, nt] at no)
        have lengths : pre.length + mid.length ≤ 13 := by
          rw [equal] at small
          change (prior ++ [Gate.mk .not b]).length ≤ 15 at small
          simp [split] at small
          omega
        have shape :
            c = ⟨pre ++ ⟨.not,a⟩ :: (mid ++ [⟨.not,b⟩]), 10 + pre.length + mid.length⟩ := by
          rw [equal, split]
          simp [List.append_assoc]
          omega
        rw [shape] at computes
        exact extractTwoNots f low high pre mid a b preFan prePos midPos lengths computes
      · have allPositive (gate : Gate) (used : gate ∈ prior) : Positive gate :=
          positiveFromFan gate (priorFan gate used).1 (fun nt => found ⟨gate,used,nt⟩)
        rw [equal] at computes
        exact (oneNotImpossible f low high prior b allPositive computes).elim
  have generalBound (f : (Fin 9 → Bool) → Bool)
      (lower : ∀ c : Circuit, FanInTwo c →
        (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 4 && x 6)) →
        circuitFun 9 c = f → 16 ≤ c.size)
      (c : Circuit) (fanin : FanInTwo c) (computes : circuitFun 9 c = f) :
      15 ≤ c.size := by
    let shiftWire (i : ℕ) : ℕ := if i < 9 then i else i + 1
    let shiftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map shiftWire⟩
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let Relation (old new : List Bool) : Prop :=
      9 ≤ old.length ∧ new.length = old.length + 1 ∧
        ∀ i, new.getD (shiftWire i) false = old.getD i false
    have relateInitial (x : Fin 9 → Bool) (value : Bool) :
        Relation (List.ofFn x) (List.ofFn x ++ [value]) := by
      refine ⟨by simp, by simp, ?_⟩
      intro i
      by_cases inside : i < 9
      · simp only [shiftWire, ite_eq_left inside]
        exact List.getD_append _ _ _ _ (by simpa using inside)
      · simp only [shiftWire, ite_eq_right inside]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have relateAppend (old new : List Bool) (value : Bool) (r : Relation old new) :
        Relation (old ++ [value]) (new ++ [value]) := by
      obtain ⟨width, length, same⟩ := r
      refine ⟨by simp; omega, by simp [length], ?_⟩
      intro i
      by_cases oldInput : i < old.length
      · have newInput : shiftWire i < new.length := by
          unfold shiftWire
          split <;> omega
        rw [List.getD_append _ _ _ _ newInput, List.getD_append _ _ _ _ oldInput]
        exact same i
      · have past : old.length ≤ i := by omega
        have shift : shiftWire i = i + 1 := ite_eq_right (by omega)
        have npast : new.length ≤ shiftWire i := by omega
        rw [List.getD_append_right _ _ _ _ npast, List.getD_append_right _ _ _ _ past, shift, length]
        congr 1
        omega
    have relateFold (gs : List Gate) (old new : List Bool) (r : Relation old new) :
        Relation (gs.foldl step old) ((gs.map shiftGate).foldl step new) := by
      induction gs generalizing old new with
      | nil => exact r
      | cons g rest ih =>
        have inputs : ((g.inputs.map shiftWire).map fun i => new.getD i false) =
            (g.inputs.map fun i => old.getD i false) := by
          rw [List.map_map]
          exact List.map_congr_left fun i _ => r.2.2 i
        apply ih (step old g) (step new (shiftGate g))
        unfold step
        change Relation (old ++ [g.op.eval (g.inputs.map fun i => old.getD i false)])
          (new ++ [g.op.eval ((g.inputs.map shiftWire).map fun i => new.getD i false)])
        rw [inputs]
        exact relateAppend old new _ r
    have preserveInitial (gs : List Gate) (wires : List Bool) (i : ℕ) (h : i < wires.length) :
        (gs.foldl step wires).getD i false = wires.getD i false := by
      induction gs generalizing wires with
      | nil => rfl
      | cons gate rest ih =>
        rw [List.foldl_cons, ih (step wires gate) (by simp [step]; omega)]
        unfold step
        exact List.getD_append _ _ _ _ h
    let prefixed (c : Circuit) : Circuit :=
      ⟨⟨.and, [4, 6]⟩ :: c.gates.map shiftGate, shiftWire c.output⟩
    have prefixIsAnd (c : Circuit) (x : Fin 9 → Bool) :
        ((prefixed c).wires (List.ofFn x)).getD 9 false = (x 4 && x 6) := by
      change ((c.gates.map shiftGate).foldl step (step (List.ofFn x) ⟨.and,[4,6]⟩)).getD 9 false = _
      rw [preserveInitial _ _ _ (by simp [step])]
      change (x 4 && (x 6 && true)) = (x 4 && x 6)
      simp
    have prefixComputes (c : Circuit) (x : Fin 9 → Bool) :
        circuitFun 9 (prefixed c) x = circuitFun 9 c x := by
      change ((c.gates.map shiftGate).foldl step (step (List.ofFn x) ⟨.and,[4,6]⟩)).getD (shiftWire c.output) false = _
      exact (relateFold c.gates _ _ (relateInitial x _)).2.2 c.output
    have minimumFromPrefix (f : (Fin 9 → Bool) → Bool)
        (lower : ∀ c : Circuit, FanInTwo c →
          (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 4 && x 6)) →
          circuitFun 9 c = f → 16 ≤ c.size)
        (c : Circuit) (fanin : FanInTwo c) (computes : circuitFun 9 c = f) :
        15 ≤ c.size := by
      have paddedFanIn : FanInTwo (prefixed c) := by
        intro g inside
        rcases List.mem_cons.mp inside with equal | inTail
        · subst g
          simp
        · obtain ⟨source, member, rfl⟩ := List.mem_map.mp inTail
          simpa [shiftGate] using fanin source member
      have paddedComputes : circuitFun 9 (prefixed c) = f := by
        ext x
        rw [prefixComputes, computes]
      have bound := lower (prefixed c) paddedFanIn (prefixIsAnd c) paddedComputes
      change 16 ≤ (Gate.mk .and [4,6] :: c.gates.map shiftGate).length at bound
      simp at bound
      change 15 ≤ c.gates.length
      omega
    exact minimumFromPrefix f lower c fanin computes
  intro C fanIn first computes
  let f := (fun x : Fin 9 → Bool =>
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2)
  have table :
      (fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) = f := by decide +kernel
  have computesList := computes.trans table
  have lower : ∀ c : Circuit, FanInTwo c →
      (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 4 && x 6)) →
      circuitFun 9 c = f → 16 ≤ c.size := by
    intro c good leading eq
    exact andLower c good leading (eq.trans table.symm)
  by_contra! small
  have exactSize : C.size = 15 := by
    have minSize := generalBound f lower C fanIn computesList
    omega
  have beforeLast : C.output < 9 + C.size := by
    by_contra! far
    change 9 + C.gates.length ≤ C.output at far
    have output := congrFun computesList (fun _ => true)
    change (C.gates.foldl step (List.ofFn (fun _ : Fin 9 => true))).getD C.output false = true at output
    rw [List.getD_eq_default _ _ (by rw [wiresLength]; simpa using far)] at output
    contradiction
  have keeps (gates : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gates.foldl step w).getD i false = w.getD i false := by
    induction gates generalizing w with
    | nil => rfl
    | cons g rest ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ h
  have outputLast : C.output + 1 = 9 + C.size := by
    by_contra early
    have shorten : C.output < 9 + (C.size - 1) := by omega
    let firstGates := C.gates.take (C.size - 1)
    let shorter : Circuit := ⟨firstGates, C.output⟩
    have length : firstGates.length = C.size - 1 := by
      change (C.gates.take (C.gates.length - 1)).length = C.gates.length - 1
      simp
    have fan : FanInTwo shorter := fun g used => fanIn g (List.mem_of_mem_take used)
    have correct : circuitFun 9 shorter = f := by
      funext x
      have agrees := congrFun computesList x
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = f x at agrees
      have split : firstGates ++ C.gates.drop (C.size - 1) = C.gates := List.take_append_drop _ _
      rw [← split, List.foldl_append, keeps _ _ _ (by rw [wiresLength, length]; simpa using shorten)] at agrees
      exact agrees
    have bound := generalBound f lower shorter fan correct
    change 15 ≤ firstGates.length at bound
    omega
  by_cases exhausted : C.gates.getLast?.map (fun g => g.op) = some .not ∧
      C.gates.countP isNot ≤ 2
  · obtain ⟨c, fan, size, correct⟩ :=
      extract f (by decide) (by decide) C fanIn computesList
        (by omega) exhausted.1 outputLast exhausted.2
    have minSize := generalBound f lower c fan (funext correct)
    omega
  · exact remaining C fanIn first computesList exactSize outputLast exhausted
