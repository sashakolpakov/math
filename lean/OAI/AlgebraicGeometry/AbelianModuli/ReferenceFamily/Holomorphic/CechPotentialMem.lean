import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechDifferential
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

/-! # Cech Potential Mem -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem

/-! A native holomorphic primitive is a literal family of holomorphic
functions whose pair differences equal the original regular cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

theorem cechPair_mem {X : Scheme.{0}} {I : Type} (U : I → X.Opens) (i j : I) (x : X)
    (hi : x ∈ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i))
    (hj : x ∈ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex j)) :
    x ∈ Cech.ExtensionCoordinates.cechIntersection U 1 (Cech.PairCoordinates.cechPairIndex i j) := by
  rw [Cech.PairCoordinates.cechIntersection_pair]
  exact ⟨(Cech.PairCoordinates.cechIntersection_singleton U i) ▸ hi, (Cech.PairCoordinates.cechIntersection_singleton U j) ▸ hj⟩

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)

structure HolomorphicCechPrimitive (z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤)) where
  coefficient (i : I) : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
    (M := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation (Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i)))
  difference (i j : I) (x : V.analyticSpace)
      (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i))
      (hj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex j)) :
    Intrinsic.CechDifferential.nativeCechValue V U 1 ⊤ z (Cech.PairCoordinates.cechPairIndex i j) x ⟨by trivial, cechPair_mem U i j _ hi hj⟩ =
      coefficient j ⟨x, hj⟩ - coefficient i ⟨x, hi⟩

namespace HolomorphicCechPrimitive

variable {V U} {z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤)} (D : HolomorphicCechPrimitive V U z)

def localPotential (W : V.carrier.Opens) (a : Γ(Cech.TermModules.cechTermModule V.carrier U 0, W))
    (r : Γ(V.carrier, W)) (i : I) : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i))) :=
  Intrinsic.CechDifferential.nativeCechCoefficient V U 0 W a (Cech.PairCoordinates.cechSingletonIndex i) -
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i))
      (V.carrier.presheaf.map (homOfLE (show W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i) ≤ W from inf_le_left)).op r) *
    DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (show DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation
      (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i)) ≤
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation (Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i)) from
          fun _ hx => hx.2) (D.coefficient i)

theorem localPotential_value (W : V.carrier.Opens) (a : Γ(Cech.TermModules.cechTermModule V.carrier U 0, W))
    (r : Γ(V.carrier, W)) (i : I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i)) :
    D.localPotential W a r i ⟨x, hx⟩ =
      Intrinsic.CechDifferential.nativeCechValue V U 0 W a (Cech.PairCoordinates.cechSingletonIndex i) x hx -
        RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hx.1 r * D.coefficient i ⟨x, hx.2⟩ := by
  change Intrinsic.CechDifferential.nativeCechCoefficient V U 0 W a (Cech.PairCoordinates.cechSingletonIndex i) ⟨x, hx⟩ -
    DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i))
      (V.carrier.presheaf.map (homOfLE (show W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i) ≤ W from inf_le_left)).op r)
        ⟨x, hx⟩ * D.coefficient i ⟨x, hx.2⟩ = _
  rw [Intrinsic.CechDifferential.nativeCechCoefficient_value]
  congr 2
  exact (Intrinsic.FrameEvaluation.sectionEvaluationOn_native V.presentation (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i)) _ ⟨x, hx⟩).trans
    (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict x.left W _ inf_le_left hx r)

end HolomorphicCechPrimitive

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive

/-! The literal extension equation and a holomorphic Cech primitive make
the local scalar potentials agree on every native overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {I : Type} {U : I → V.carrier.Opens}
    {z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤)} (D : HolomorphicCechPrimitive V U z)

theorem localPotential_compatible (W : V.carrier.Opens)
    (a : Γ(Cech.TermModules.cechTermModule V.carrier U 0, W)) (r : Γ(V.carrier, W))
    (heq : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 0).app W a =
      r • (Cech.TermModules.cechTermModule V.carrier U 1).presheaf.map W.leTop.op z)
    (i j : I) (x : V.analyticSpace)
    (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i))
    (hj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex j)) :
    D.localPotential W a r i ⟨x, hi⟩ = D.localPotential W a r j ⟨x, hj⟩ := by
  rw [D.localPotential_value, D.localPotential_value]
  let q := Cech.PairCoordinates.cechPairIndex i j
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 1 q :=
    ⟨hi.1, cechPair_mem U i j _ hi.2 hj.2⟩
  have h0 := Intrinsic.CechDifferential.nativeCechValue_congr_index V U 0 W a (Cech.PairCoordinates.cechPairIndex_face_zero i j) x
    (show ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.ExtensionCoordinates.cechFaceIndex 0 0 q) from
      ⟨hx.1, Cech.ExtensionCoordinates.cechIntersection_le_face U 0 0 q hx.2⟩) hj
  have h1 := Intrinsic.CechDifferential.nativeCechValue_congr_index V U 0 W a (Cech.PairCoordinates.cechPairIndex_face_one i j) x
    (show ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.ExtensionCoordinates.cechFaceIndex 0 1 q) from
      ⟨hx.1, Cech.ExtensionCoordinates.cechIntersection_le_face U 0 1 q hx.2⟩) hi
  have hd := (Intrinsic.CechDifferential.nativeCechValue_differential_zero V U W a q x hx).trans (congrArg₂ (· - ·) h0 h1)
  have hs := (congrArg (fun b : Γ(Cech.TermModules.cechTermModule V.carrier U 1, W) =>
    Intrinsic.CechDifferential.nativeCechValue V U 1 W b q x hx) heq).trans
      ((Intrinsic.CechDifferential.nativeCechValue_smul V U 1 W r _ q x hx).trans
        (congrArg (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hx.1 r * ·)
          (Intrinsic.CechDifferential.nativeCechValue_restrict V U 1 (show W ≤ ⊤ from le_top) z q x hx)))
  have h := hd.symm.trans hs
  change Intrinsic.CechDifferential.nativeCechValue V U 0 W a (Cech.PairCoordinates.cechSingletonIndex j) x hj -
      Intrinsic.CechDifferential.nativeCechValue V U 0 W a (Cech.PairCoordinates.cechSingletonIndex i) x hi =
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hi.1 r *
      Intrinsic.CechDifferential.nativeCechValue V U 1 ⊤ z (Cech.PairCoordinates.cechPairIndex i j) x ⟨by trivial, cechPair_mem U i j _ hi.2 hj.2⟩ at h
  rw [D.difference i j x hi.2 hj.2] at h
  linear_combination -h

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem.HolomorphicCechPrimitive

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem

/-! Compatible local Cech potentials glue to an actual holomorphic
function on every prescribed native algebraic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

theorem cechSingleton_cover {X : Scheme.{0}} {I : Type} (U : I → X.Opens) (hU : iSup U = ⊤)
    (x : X) : ∃ i, x ∈ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i) := by
  have hx : x ∈ iSup U := hU.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨i, (Cech.PairCoordinates.cechIntersection_singleton U i).symm ▸ hi⟩

namespace HolomorphicCechPrimitive

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {I : Type} {U : I → V.carrier.Opens}
    {z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤)} (D : HolomorphicCechPrimitive V U z) (hU : iSup U = ⊤)
    (W : V.carrier.Opens) (a : Γ(Cech.TermModules.cechTermModule V.carrier U 0, W)) (r : Γ(V.carrier, W))
    (heq : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 0).app W a =
      r • (Cech.TermModules.cechTermModule V.carrier U 1).presheaf.map W.leTop.op z)

include hU heq

theorem exists_potential :
    ∃ f : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W),
      ∀ (i : I) (x : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation
        (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i))),
        f ⟨x.val, x.property.1⟩ = D.localPotential W a r i x := by
  let A (i : I) := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation
    (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i))
  have hcover : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W ≤ iSup A := by
    intro x hx
    obtain ⟨i, hi⟩ := cechSingleton_cover U hU (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  obtain ⟨f, hf⟩ := DivisorClass.Chern.Holomorphic.FunctionGluing.exists_holomorphicFunction_glue A (D.localPotential W a r)
    (D.localPotential_compatible W a r heq)
  exact ⟨DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction hcover f, hf⟩

def potential : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) :=
  Classical.choose (D.exists_potential hU W a r heq)

theorem potential_value (i : I) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i)) :
    D.potential hU W a r heq ⟨x, hx.1⟩ =
      Intrinsic.CechDifferential.nativeCechValue V U 0 W a (Cech.PairCoordinates.cechSingletonIndex i) x hx -
        RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hx.1 r * D.coefficient i ⟨x, hx.2⟩ :=
  (Classical.choose_spec (D.exists_potential hU W a r heq) i ⟨x, hx⟩).trans
    (D.localPotential_value W a r i x hx)

end HolomorphicCechPrimitive

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialMem

end

end OAI
