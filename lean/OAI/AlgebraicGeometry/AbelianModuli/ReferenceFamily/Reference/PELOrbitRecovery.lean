import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELArithmeticRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.MapKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodPointDetection

/-! # PEL Orbit Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The principal arithmetic element recovered from an actual PEL
isomorphism carries the original source ball point exactly to the target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] [Field K]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {G : Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    {W : AlgebraicModel.ReferenceAlgebraicModel G hP} {D' : DualModel.ReferenceDualModel G hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M D} {q : IsogenyKernel.ReferenceLatticeIsogeny W D'}
    (C : PicardConstruction.ReferencePicardConstruction p) (C' : PicardConstruction.ReferencePicardConstruction q)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N]
    (e : PEL.Objects.PELIso (C.pelObject iota κ he N) (C'.pelObject iota κ he N))

theorem PicardConstruction.ReferencePicardConstruction.referenceFieldIso_point : w.val = P.lineAction (C.referenceFieldIso C' iota κ he N e) z.val := by
  let f : M.abelian.toOver ⟶ W.abelian.toOver := e.polarized.abelian.hom
  let : IsMonHom f := e.polarized.abelianGroup
  exact P.referencePeriodPoint_of_action_mem hP (C.referenceFieldIso C' iota κ he N e)
    (C.referenceFieldIso_unitary C' iota κ he N e) z w
    (M.referenceAmbientAction_mem_of_native_map W (C.referenceFieldIso C' iota κ he N e) f
      (C.referenceFieldIso_marking C' iota κ he N e))

include e in
theorem PicardConstruction.ReferencePicardConstruction.principalOrbit_of_pelIso (hN : 3 ≤ N) :
    P.OrbitRelation (Groups.principalSpecialUnitary P.b P.lattice N) z w :=
  ⟨C.referenceFieldIso C' iota κ he N e, C.referenceFieldIso_principal C' iota κ he N e hN,
    C.referenceFieldIso_point C' iota κ he N e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
