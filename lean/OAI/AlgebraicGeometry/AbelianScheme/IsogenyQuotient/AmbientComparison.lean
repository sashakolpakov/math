import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Inclusion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Ambient Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmbientComparison.Construction

noncomputable section

/-!
Compare the ambient group built from the relative point functor with the
ordinary scheme pullback used by ReferenceFamily. This keeps the represented group
law and the native pullback group law connected by actual group maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v w

section Equivalence

variable {C : Type*} {D : Type*} [Category.{v} C] [Category.{w} D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  (e : C ≌ D) [e.functor.Monoidal] (G : C) [GrpObj G] (X : D)

/-- A Cartesian equivalence preserves the groups of test-object points,
including tests not literally in the functor's image. -/
def equivalencePointMulEquiv :
    (X ⟶ e.functor.obj G) ≃* (e.inverse.obj X ⟶ G) :=
  (((yonedaGrpObj (e.functor.obj G)).mapIso (e.counitIso.app X).op).groupIsoToMulEquiv).trans
    (MulEquiv.ofBijective (e.functor.homMonoidHom (X := e.inverse.obj X) (M := G))
      ⟨e.functor.map_injective, e.functor.map_surjective⟩).symm

theorem equivalencePointMulEquiv_map (x : X ⟶ e.functor.obj G) :
    e.functor.map (equivalencePointMulEquiv e G X x) = (e.counitIso.app X).hom ≫ x := by
  exact (MulEquiv.ofBijective (e.functor.homMonoidHom (X := e.inverse.obj X) (M := G))
    ⟨e.functor.map_injective, e.functor.map_surjective⟩).apply_symm_apply _

end Equivalence

variable {S : Scheme.{u}} (A P : Over S) [GrpObj A] [IsCommMonObj A]

local instance : CartesianMonoidalCategory (Over P) := Over.cartesianMonoidalCategory P
local instance : BraidedCategory (Over P) := Over.braidedCategory P

/-- The represented ambient point group, over a test of the parameter,
identified with the original ambient points on that test. -/
def ambientPointMulEquiv (T : Over P.left) :
    (T ⟶ (Kernel.Inclusion.Construction.ambientGroupScheme A P).X) ≃* (((Over.map P.hom).obj T) ⟶ A) := by
  let e := Over.iteratedSliceEquiv P
  letI : e.functor.Braided := Functor.Braided.ofChosenFiniteProducts e.functor
  let G := Kernel.Inclusion.Construction.relativeAmbientCommGroup (A := A) (P := P)
  let h := equivalencePointMulEquiv e G.X T
  let j := (yonedaGrpObjIsoOfRepresentableBy G.X
    (IsogenyQuotient.Subgroup.Construction.relativePointGroups (Kernel.Inclusion.Construction.fullRelativeSubgroup A P) ⋙ forget₂ CommGrpCat GrpCat)
    Kernel.Inclusion.Construction.ambientPointGroups_representable).app (.op (e.inverse.obj T))
  exact (h.trans j.groupIsoToMulEquiv).trans Subgroup.topEquiv

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointMulEquiv_left (T : Over P.left) (x : T ⟶ (Kernel.Inclusion.Construction.ambientGroupScheme A P).X) :
    (ambientPointMulEquiv A P T x).left = x.left ≫ pullback.snd P.hom A.hom := by
  let e := Over.iteratedSliceEquiv P
  let : e.functor.Braided := Functor.Braided.ofChosenFiniteProducts e.functor
  let G := Kernel.Inclusion.Construction.relativeAmbientCommGroup (A := A) (P := P)
  have hx := congrArg (fun a => a.left) (equivalencePointMulEquiv_map e G.X T x)
  change (equivalencePointMulEquiv e G.X T x).left.left = (𝟙 T.left) ≫ x.left at hx
  rw [Category.id_comp] at hx
  change (equivalencePointMulEquiv e G.X T x).left.left ≫ pullback.snd P.hom A.hom = _
  rw [hx]

omit [GrpObj A] [IsCommMonObj A] in
/-- The underlying comparison is the actual symmetry of the pullback
square, regarded as a morphism over the parameter. -/
def ambientPullbackIso {dim : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim S) :
    (Kernel.Inclusion.Construction.ambientGroupScheme B.scheme P).X ≅ (B.pullback P.hom).scheme :=
  Over.isoMk (pullbackSymmetry P.hom B.scheme.hom)
    (pullbackSymmetry_hom_comp_snd P.hom B.scheme.hom)

omit [GrpObj A] [IsCommMonObj A] in
set_option backward.isDefEq.respectTransparency false in
theorem ambientPullbackIso_points {dim : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim S)
    (T : Over P.left) (x : T ⟶ (Kernel.Inclusion.Construction.ambientGroupScheme B.scheme P).X) :
    B.baseChangePointsMulEquiv P.hom T (x ≫ (ambientPullbackIso P B).hom) =
      ambientPointMulEquiv B.scheme P T x := by
  apply Over.OverMorphism.ext
  rw [ambientPointMulEquiv_left]
  change (x.left ≫ (pullbackSymmetry P.hom B.scheme.hom).hom) ≫
    pullback.fst B.scheme.hom P.hom = x.left ≫ pullback.snd P.hom B.scheme.hom
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]

omit [GrpObj A] [IsCommMonObj A] in
set_option backward.isDefEq.respectTransparency false in
/-- Both ambient group laws are the same under the canonical scheme
comparison, because their test-object point equivalences preserve products. -/
theorem ambientPullbackIso_isMonHom {dim : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim S) :
    IsMonHom (ambientPullbackIso P B).hom := by
  apply GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    apply (B.baseChangePointsMulEquiv P.hom T).injective
    rw [ambientPullbackIso_points, map_one, map_one]
  · intro T x y
    apply (B.baseChangePointsMulEquiv P.hom T).injective
    rw [ambientPullbackIso_points, map_mul, map_mul,
      ambientPullbackIso_points, ambientPullbackIso_points]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmbientComparison.Construction
