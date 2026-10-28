import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentHopfLift
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base

/-! # Etale Target Maps -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleTargetMaps.Components

noncomputable section

/-!
HenselianLifting as a uniqueness theorem for actual scheme maps into an etale target.
Equality after native special-fiber pullback is tested on the residue
coordinate scheme and converted to the proved algebraic uniqueness.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [HenselianLocalRing R]

def affineOver (A : Type u) [CommRing A] [Algebra R A] : Over (Spec (.of R)) :=
  (algSpec (.of R)).obj (.op (CommAlgCat.of R A))

def affineMap {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : affineOver R B ⟶ affineOver R A :=
  (algSpec (.of R)).map (CommAlgCat.ofHom f).op

variable (A : Type u) [CommRing A] [Algebra R A]

/-- The residue coordinate scheme is an actual test scheme over the
closed point, with the arithmetic square proved. -/
def residueCoordinateTest : affineOver R (ComponentLifts.Components.ResidueAlgebra R A) ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := by
  letI : Algebra (IsLocalRing.ResidueField R) (ComponentLifts.Components.ResidueAlgebra R A) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  refine Over.homMk (Spec.map (CommRingCat.ofHom
    (algebraMap (IsLocalRing.ResidueField R) (ComponentLifts.Components.ResidueAlgebra R A)))) ?_
  change Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) (ComponentLifts.Components.ResidueAlgebra R A))) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) =
    Spec.map (CommRingCat.ofHom (algebraMap R (ComponentLifts.Components.ResidueAlgebra R A)))
  rw [← Spec.map_comp]
  rfl

variable {C : Type u} [CommRing C] [Algebra R C] [Module.Finite R A]
variable [Module.Finite R C] [Algebra.Etale R C]

omit [HenselianLocalRing R] [Module.Finite R C] [Algebra.Etale R C] in
theorem affineMap_injective {B : Type u} [CommRing B] [Algebra R B]
    {f g : C →ₐ[R] B} (h : affineMap R f = affineMap R g) : f = g := by
  have he := (algSpec.fullyFaithful (R := .of R)).map_injective h
  exact congrArg (fun a => a.unop.hom) he

omit [Module.Finite R C] in
/-- Equality of special fibers determines the actual map from a finite
affine scheme into a finite etale target. The source may be non-etale. -/
theorem affine_specialization_injective (f g : C →ₐ[R] A)
    (h : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map (affineMap R f) =
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map (affineMap R g)) :
    f = g := by
  apply OAI.Algebra.LocalRing.HenselianLifting.Construction.unramified_hom_ext_of_quotient R C _
    (OAI.Algebra.LocalRing.HenselianLifting.Construction.maximalIdeal_map_le_jacobson R A)
  have he := Kernel.Base.maps_equal_on_special_tests
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) (affineMap R f) (affineMap R g) h
    (affineOver R (ComponentLifts.Components.ResidueAlgebra R A)) (residueCoordinateTest R A)
    (affineMap R (ComponentHopfLift.Components.residueProjection R A))
  apply affineMap_injective R
  exact ((algSpec (.of R)).map_comp (CommAlgCat.ofHom (ComponentHopfLift.Components.residueProjection R A)).op
    (CommAlgCat.ofHom f).op).trans (he.trans
      ((algSpec (.of R)).map_comp (CommAlgCat.ofHom (ComponentHopfLift.Components.residueProjection R A)).op
        (CommAlgCat.ofHom g).op).symm)

/-- An arbitrary residue-coordinate map to the finite etale target lifts
uniquely as an actual affine scheme morphism. -/
theorem affine_residue_lift (φ : C →ₐ[R] ComponentLifts.Components.ResidueAlgebra R A) :
    ∃! f : affineOver R A ⟶ affineOver R C,
      affineMap R (ComponentHopfLift.Components.residueProjection R A) ≫ f = affineMap R φ := by
  obtain ⟨f, hf, hu⟩ := OAI.Algebra.LocalRing.HenselianLifting.Construction.finiteEtale_hom_lift R C A φ
  refine ⟨affineMap R f, ?_, ?_⟩
  · exact ((algSpec (.of R)).map_comp (CommAlgCat.ofHom (ComponentHopfLift.Components.residueProjection R A)).op
      (CommAlgCat.ofHom f).op).symm.trans (congrArg (affineMap R) hf)
  · intro g hg
    let a : C →ₐ[R] A := ((algSpec.fullyFaithful (R := .of R)).preimage g).unop.hom
    have ha : affineMap R a = g := (algSpec.fullyFaithful (R := .of R)).map_preimage g
    have har : (ComponentHopfLift.Components.residueProjection R A).comp a = φ := by
      apply affineMap_injective R
      exact ((algSpec (.of R)).map_comp (CommAlgCat.ofHom (ComponentHopfLift.Components.residueProjection R A)).op
        (CommAlgCat.ofHom a).op).trans
          ((congrArg (fun f => affineMap R (ComponentHopfLift.Components.residueProjection R A) ≫ f) ha).trans hg)
    exact ha.symm.trans (congrArg (affineMap R) (hu a har))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleTargetMaps.Components
