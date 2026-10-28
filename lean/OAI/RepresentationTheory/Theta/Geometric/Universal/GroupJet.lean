import OAI.RepresentationTheory.Theta.Geometric.Universal.DifferentialJet
import OAI.RepresentationTheory.Theta.Geometric.TangentNeighborhoods
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Group Jet -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.GroupJet

noncomputable section

/-! Subtracting the constant affine test point from its universal jet
gives an actual infinitesimal point at the identity of a group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] DifferentialJet.differentialOppositeModule

def differentialJetTest (R : CommAlgCat.{0} ℂ) : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (CommAlgCat.of ℂ (DifferentialJet.differentialJetRing R))

def differentialJetOrigin (R : CommAlgCat.{0} ℂ) : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ differentialJetTest R :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (TrivSqZeroExt.fstHom ℂ R (KaehlerDifferential ℂ R)))

def differentialJetProjection (R : CommAlgCat.{0} ℂ) : differentialJetTest R ⟶ AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom ℂ R (KaehlerDifferential ℂ R)))

def differentialJetPoint (R : CommAlgCat.{0} ℂ) : differentialJetTest R ⟶ AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (DifferentialJet.differentialJet R))

theorem differentialJetOrigin_projection (R : CommAlgCat.{0} ℂ) :
    differentialJetOrigin R ≫ differentialJetProjection R = 𝟙 (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp]
  exact Spec.map_id _

theorem differentialJetOrigin_point (R : CommAlgCat.{0} ℂ) :
    differentialJetOrigin R ≫ differentialJetPoint R = 𝟙 (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp]
  exact Spec.map_id _

theorem differentialJetOrigin_surjective (R : CommAlgCat.{0} ℂ) :
    Function.Surjective (differentialJetOrigin R).left := by
  let f := (TrivSqZeroExt.fstHom ℂ R (KaehlerDifferential ℂ R)).toRingHom
  change Function.Surjective (PrimeSpectrum.comap f)
  intro p
  change p ∈ Set.range (PrimeSpectrum.comap f)
  rw [range_comap_of_surjective R f TrivSqZeroExt.fst_surjective]
  intro z hz
  have he : z.fst = 0 := hz
  have hs : z * z = 0 := by
    apply TrivSqZeroExt.ext
    · change z.fst * z.fst = 0
      rw [he, zero_mul]
    · change z.fst • z.snd + z.fst • z.snd = 0
      rw [he, zero_smul, zero_add]
  exact (p.isPrime.mem_or_mem (hs ▸ p.asIdeal.zero_mem)).elim id id

variable {G : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G]

def universalGroupJet (R : CommAlgCat.{0} ℂ) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    differentialJetTest R ⟶ G :=
  (differentialJetProjection R ≫ x)⁻¹ * (differentialJetPoint R ≫ x)

theorem universalGroupJet_origin (R : CommAlgCat.{0} ℂ) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    differentialJetOrigin R ≫ universalGroupJet R x = 1 := by
  rw [universalGroupJet, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    ← Category.assoc, differentialJetOrigin_projection, differentialJetOrigin_point,
    Category.id_comp, inv_mul_cancel]

def differentialJetSchemeMap {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) :
    differentialJetTest S ⟶ differentialJetTest R :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (DifferentialJet.differentialJetMap f))

theorem differentialJetSchemeMap_point {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) :
    differentialJetSchemeMap f ≫ differentialJetPoint R =
      differentialJetPoint S ≫ AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap f := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g.toRingHom)) (DifferentialJet.differentialJetMap_jet f)

theorem differentialJetSchemeMap_projection {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) :
    differentialJetSchemeMap f ≫ differentialJetProjection R =
      differentialJetProjection S ≫ AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap f := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g.toRingHom)) (DifferentialJet.differentialJetMap_inl f)

theorem universalGroupJet_naturality {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S)
    (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    differentialJetSchemeMap f ≫ universalGroupJet R x =
      universalGroupJet S (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap f ≫ x) := by
  rw [universalGroupJet, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    ← Category.assoc, differentialJetSchemeMap_projection, differentialJetSchemeMap_point]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.GroupJet
