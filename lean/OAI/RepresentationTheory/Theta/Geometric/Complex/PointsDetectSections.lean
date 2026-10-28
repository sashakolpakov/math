import OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation
import OAI.AlgebraicGeometry.Albanese.Construction.ProjectiveCoordinates
import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints

/-! # Points Detect Sections -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections

noncomputable section

/-! Complex points detect algebraic opens and regular sections on reduced
schemes locally of finite type over C. This permits gluing by identities
verified in the period coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem opens_le_of_complex_points (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom]
    (U V : X.left.Opens)
    (h : ∀ p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X,
      p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U → p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ V) : U ≤ V := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  intro x hx
  by_contra hxV
  have hne : ((U : Set X.left) ∩ (V : Set X.left)ᶜ).Nonempty := ⟨x, hx, hxV⟩
  have hlc : IsLocallyClosed ((U : Set X.left) ∩ (V : Set X.left)ᶜ) :=
    U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hne hlc
  change IsClosed {y} at hyc
  let p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
    Over.homMk (pointOfClosedPoint X.hom y hyc) (pointOfClosedPoint_comp X.hom y hyc)
  have hp : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) = y :=
    pointOfClosedPoint_apply X.hom y hyc _
  have hpU : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U := by
    rw [hp]
    exact hy.1
  have hpV := h p hpU
  rw [hp] at hpV
  exact hy.2 hpV

theorem opens_eq_of_complex_points (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom]
    (U V : X.left.Opens)
    (h : ∀ p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X,
      p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U ↔ p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ V) : U = V :=
  le_antisymm (opens_le_of_complex_points X U V (fun p => (h p).mp))
    (opens_le_of_complex_points X V U (fun p => (h p).mpr))

theorem complexSectionValue_mem_basicOpen {X : Scheme} (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X)
    (r : Γ(X, ⊤)) : p (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ X.basicOpen r ↔
      SectionEvaluation.complexSectionValue p ⊤ (by trivial) r ≠ 0 := by
  have h := AlgebraicGeometry.Albanese.Construction.ProjectiveCoordinates.pointEvaluate_mem_basicOpen p r
  rw [Subsingleton.elim (IsLocalRing.closedPoint ℂ) (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)] at h
  exact h

theorem complexSectionValue_top_ext (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [IsReduced X.left] (s t : Γ(X.left, ⊤))
    (h : ∀ p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X,
      SectionEvaluation.complexSectionValue p.left ⊤ (by trivial) s = SectionEvaluation.complexSectionValue p.left ⊤ (by trivial) t) :
    s = t := by
  apply sub_eq_zero.mp
  apply eq_zero_of_basicOpen_eq_bot
  apply le_antisymm _ bot_le
  apply opens_le_of_complex_points X
  intro p hp
  have hn := (complexSectionValue_mem_basicOpen p.left (s - t)).mp hp
  exact False.elim (hn (by rw [map_sub, h p, sub_self]))

theorem complexSectionValue_ext (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [IsReduced X.left] (U : X.left.Opens) (s t : Γ(X.left, U))
    (h : ∀ (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hp : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U),
      SectionEvaluation.complexSectionValue p.left U hp s = SectionEvaluation.complexSectionValue p.left U hp t) : s = t := by
  let Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (U.ι ≫ X.hom)
  let : LocallyOfFiniteType Y.hom := by
    change LocallyOfFiniteType (U.ι ≫ X.hom)
    infer_instance
  let : IsReduced Y.left := by
    change IsReduced U.toScheme
    infer_instance
  have he : U.topIso.inv s = U.topIso.inv t := by
    apply complexSectionValue_top_ext Y
    intro p
    let q : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := p ≫ Over.homMk U.ι rfl
    have hq := h q (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).property
    exact (SectionEvaluation.complexSectionValue_open U p.left s).symm.trans
      (hq.trans (SectionEvaluation.complexSectionValue_open U p.left t))
  have hh := congrArg (fun a => U.topIso.hom a) he
  simpa only [Iso.inv_hom_id_apply] using hh

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections
