import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CoverRepresentability
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupFunctor
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Open Gluing Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Effective gluing of the scheme representing the homogeneous Picard
sheaf. Local dual data give an actual global abelian scheme representing
the same original sheaf, with native comparisons on every base chart.
Construction of the normalized universal line is a separate step. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupFunctor.Construction
open scoped _root_.CategoryTheory.MonObj
universe u

variable {g : ℕ} {S : Scheme.{u}}

theorem Abelian.Schemes.AbelianScheme.homogeneousPicard_isSheaf_zariski (A : Abelian.Schemes.AbelianScheme g S) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) A.homogeneousPicardSheaf.obj := by
  have hz : Scheme.zariskiTopology ≤ Scheme.fppfTopology :=
    Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
  apply Presieve.isSheaf_of_le _ _
    ((isSheaf_iff_isSheaf_of_type _ _).mp A.homogeneousPicardSheaf.property)
  intro T R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact hz _ hR

namespace Dual.OpenGluingScheme.DualOpenGluing

variable (A : Abelian.Schemes.AbelianScheme g S) (U : S.OpenCover.{u})
  (D : ∀ j, Data.DualAbelianData (A.pullback (U.f j)))

def localRepresentable (j : U.I₀) :
    ((Over.map (U.f j)).op ⋙ A.homogeneousPicardSheaf.obj).RepresentableBy
      (D j).abelian.scheme :=
  (D j).representable.ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over (U.X j)) (Type (u + 1))).mapIso
      (A.homogeneousPicardSheafBaseChangeIso (U.f j)))

def scheme : Over S :=
  Open.CoverRepresentability.OpenCoverRepresentability.scheme A.homogeneousPicardSheaf.obj U
    (fun j => (D j).abelian.scheme) (localRepresentable A U D)
    A.homogeneousPicard_isSheaf_zariski

def representable : A.homogeneousPicardSheaf.obj.RepresentableBy (DualOpenGluing.scheme A U D) :=
  Open.CoverRepresentability.OpenCoverRepresentability.representable A.homogeneousPicardSheaf.obj U
    (fun j => (D j).abelian.scheme) (localRepresentable A U D)
    A.homogeneousPicard_isSheaf_zariski

def chartIso (j : U.I₀) :
    (D j).abelian.scheme ≅ (Over.pullback (U.f j)).obj (DualOpenGluing.scheme A U D) :=
  Open.CoverRepresentability.OpenCoverRepresentability.chartPullbackIso A.homogeneousPicardSheaf.obj U
    (fun j => (D j).abelian.scheme) (localRepresentable A U D)
    A.homogeneousPicard_isSheaf_zariski j

theorem proper : IsProper (DualOpenGluing.scheme A U D).hom :=
  Open.CoverRepresentability.OpenCoverRepresentability.localProperty A.homogeneousPicardSheaf.obj U
    (fun j => (D j).abelian.scheme) (localRepresentable A U D)
    A.homogeneousPicard_isSheaf_zariski (@IsProper)
    (fun j => (D j).abelian.proper)

theorem smoothDimension : SmoothOfRelativeDimension g (DualOpenGluing.scheme A U D).hom := by
  let : IsZariskiLocalAtTarget
      (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @SmoothOfRelativeDimension g)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g))
  exact Open.CoverRepresentability.OpenCoverRepresentability.localProperty A.homogeneousPicardSheaf.obj U
    (fun j => (D j).abelian.scheme) (localRepresentable A U D)
    A.homogeneousPicard_isSheaf_zariski (@SmoothOfRelativeDimension g)
    (fun j => (D j).abelian.smoothDimension)

theorem connected : GeometricallyConnected (DualOpenGluing.scheme A U D).hom := by
  let : IsZariskiLocalAtTarget
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  exact Open.CoverRepresentability.OpenCoverRepresentability.localProperty A.homogeneousPicardSheaf.obj U
    (fun j => (D j).abelian.scheme) (localRepresentable A U D)
    A.homogeneousPicard_isSheaf_zariski (@GeometricallyConnected)
    (fun j => (D j).abelian.connected)

def groupRepresentable :
    ((Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupFunctor A ⋙ forget₂ CommGrpCat GrpCat) ⋙
      forget GrpCat).RepresentableBy (DualOpenGluing.scheme A U D) :=
  (DualOpenGluing.representable A U D).ofIso (Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupForgetIso A).symm

@[instance_reducible]
def group : GrpObj (DualOpenGluing.scheme A U D) :=
  GrpObj.ofRepresentableBy (DualOpenGluing.scheme A U D)
    (Picard.Homomorphisms.GroupFunctor.Construction.homogeneousPicardGroupFunctor A ⋙ forget₂ CommGrpCat GrpCat)
    (groupRepresentable A U D)

def groupHomEquiv (T : Over S) :
    letI := DualOpenGluing.group A U D
    (T ⟶ DualOpenGluing.scheme A U D) ≃* A.homogeneousPicardSheaf.obj.obj (.op T) := by
  letI := DualOpenGluing.group A U D
  let a := groupRepresentable A U D
  refine { toEquiv := a.homEquiv', map_mul' := ?_ }
  intro x y
  change a.homEquiv' (lift x y ≫ a.homEquiv'.symm
      (a.homEquiv' (fst (DualOpenGluing.scheme A U D) (DualOpenGluing.scheme A U D)) *
        a.homEquiv' (snd (DualOpenGluing.scheme A U D) (DualOpenGluing.scheme A U D)))) =
    a.homEquiv' x * a.homEquiv' y
  simp only [a.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
  simp only [← a.homEquiv'_comp]
  simp

theorem group_commutative :
    letI := DualOpenGluing.group A U D
    IsCommMonObj (DualOpenGluing.scheme A U D) := by
  let : GrpObj (DualOpenGluing.scheme A U D) := DualOpenGluing.group A U D
  apply (isCommMonObj_iff_isMulCommutative (DualOpenGluing.scheme A U D)).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (groupHomEquiv A U D T).injective
  rw [map_mul, map_mul, mul_comm]

def abelian : Abelian.Schemes.AbelianScheme g S where
  scheme := DualOpenGluing.scheme A U D
  group := DualOpenGluing.group A U D
  commutative := group_commutative A U D
  proper := DualOpenGluing.proper A U D
  smoothDimension := DualOpenGluing.smoothDimension A U D
  connected := DualOpenGluing.connected A U D

theorem origin (T : Over S) :
    (DualOpenGluing.representable A U D).homEquiv (1 : T ⟶ (DualOpenGluing.abelian A U D).scheme) =
      A.trivialHomogeneousPicardClass T := by
  let : GrpObj (DualOpenGluing.scheme A U D) := DualOpenGluing.group A U D
  rw [Picard.Homomorphisms.HomogeneousGroup.Construction.trivialHomogeneousPicardClass_eq_one]
  exact (groupHomEquiv A U D T).map_one

end Dual.OpenGluingScheme.DualOpenGluing

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
