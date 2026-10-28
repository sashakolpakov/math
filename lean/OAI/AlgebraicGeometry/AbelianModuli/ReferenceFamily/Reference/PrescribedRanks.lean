import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.GeometricLieRank
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects

/-! # Prescribed Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Every constructed reference algebraic fiber satisfies the literal
PEL Lie-signature condition on every algebraically closed test field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)
    {K : Type} [Field K] [NumberField K]
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ)

include he in
omit [NumberField K] in
theorem AlgebraicModel.ReferenceAlgebraicModel.hasPrescribedLieRanks : PEL.Objects.HasPrescribedLieRanks P iota
    (Over.mk (Spec.map (CommRingCat.ofHom κ))) M.abelianScheme M.integralAction := by
  intro k _ _ j p hp σ
  let j' : ℂ →+* k := (Spec.preimage p).hom
  have hj' : Spec.map (CommRingCat.ofHom j') = p := Spec.map_preimage p
  have hc : j'.comp κ = j := by
    have hs : Spec.map (CommRingCat.ofHom (j'.comp κ)) = Spec.map (CommRingCat.ofHom j) := by
      change Spec.map (CommRingCat.ofHom κ ≫ CommRingCat.ofHom j') = _
      rw [Spec.map_comp, hj']
      exact hp
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  let : Algebra ℂ k := j'.toAlgebra
  have hr := M.hasGeometricLieRank k σ
  have hbase : RepresentationTheory.Theta.Geometric.LieFieldTests.fieldBaseMap ℂ k = p := hj'
  rw [hbase] at hr
  have hchar : AlgebraicModel.ReferenceAlgebraicModel.geometricCharacter k (P.μ.comp σ.toRingHom) =
      (j.comp iota).comp (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) := by
    apply RingHom.ext
    intro a
    change j' (P.μ (σ (a : E))) = j (iota (σ (a : E)))
    exact (congrArg j' (congrArg (fun f : E →+* ℂ => f (σ (a : E))) he.symm)).trans
      (congrArg (fun f : K →+* k => f (iota (σ (a : E)))) hc)
  rw [hchar] at hr
  exact hr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
