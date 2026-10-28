import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ClosedPointIrreducibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.PointTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedRationalPoints

/-! # Closed Integrality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! Rational translations act transitively on closed points of an abelian
scheme over an algebraically closed field. Connectedness then gives integrality. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {K : Type u} [Field K] {g : ℕ} (A : Schemes.AbelianScheme g (Spec (.of K)))

theorem Schemes.AbelianScheme.point_comp_basePointTranslation
    (a b : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    a ≫ A.basePointTranslation b = b * a := by
  simp [Schemes.AbelianScheme.basePointTranslation, MonObj.comp_mul]

theorem Schemes.AbelianScheme.irreducible_overAlgClosed [IsAlgClosed K] : IrreducibleSpace A.scheme.left := by
  have : ConnectedSpace A.scheme.left := A.connected_overField
  have : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  have : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  have : IsNoetherian A.scheme.left := ⟨⟩
  have : JacobsonSpace A.scheme.left := LocallyOfFiniteType.jacobsonSpace A.scheme.hom
  apply Homogeneous.ClosedPointIrreducibility.irreducibleSpace_of_homogeneous_closedPoints
  intro x y hx hy
  let a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme :=
    Over.homMk (pointOfClosedPoint A.scheme.hom x hx) (pointOfClosedPoint_comp A.scheme.hom x hx)
  let b : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme :=
    Over.homMk (pointOfClosedPoint A.scheme.hom y hy) (pointOfClosedPoint_comp A.scheme.hom y hy)
  let c := a⁻¹ * b
  let E := A.basePointTranslationIso c
  have he : a ≫ E.hom = b := by
    change a ≫ A.basePointTranslation c = b
    rw [Schemes.AbelianScheme.point_comp_basePointTranslation]
    simp [c, mul_comm]
  have : IsIso E.hom.left := (Over.forget _).map_isIso E.hom
  refine ⟨E.hom.left.homeomorph, ?_⟩
  have hpoint := congrArg (fun f : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme =>
    f.left (IsLocalRing.closedPoint K)) he
  change E.hom.left (a.left (IsLocalRing.closedPoint K)) = b.left (IsLocalRing.closedPoint K) at hpoint
  have ha : a.left (IsLocalRing.closedPoint K) = x :=
    pointOfClosedPoint_apply A.scheme.hom x hx _
  have hb : b.left (IsLocalRing.closedPoint K) = y :=
    pointOfClosedPoint_apply A.scheme.hom y hy _
  rw [ha, hb] at hpoint
  change E.hom.left x = y
  exact hpoint

theorem Schemes.AbelianScheme.integral_overAlgClosed [IsAlgClosed K] : IsIntegral A.scheme.left := by
  have : IsReduced A.scheme.left := A.reduced_overField
  have : IrreducibleSpace A.scheme.left := A.irreducible_overAlgClosed
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
