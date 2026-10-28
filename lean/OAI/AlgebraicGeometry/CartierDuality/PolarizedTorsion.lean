import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Block
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterSheaf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Naturality
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SliceCharacters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.BaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualMaps
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroups
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCategory
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffinePullback
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineSheafIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterFunctor
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SmallCharacters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeGluing
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeRepresentabilityP
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalRepresentatives
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentabilityDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupRepresentatives
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCharacterGroups
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineEvaluationInv
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.BidualCriterionEq
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentationMorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EvaluationBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalIsomorphismsIs
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBidual
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafQuotients
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicQuotients
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.QuotientRepresentability
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DoubleAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AnnihilatorBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteLocallyFreeCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafRetracts
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionGeometry
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FrobeniusReduction
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Torsion
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRankAnnihilation
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeCoprimeTorsion
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeTorsion
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveLineDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineIntrinsicLineDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ScalarLineGluing
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfScalarsOf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterGluing
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DescentRelationMorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicInvariantDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicDescentRecovery
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedRecovery
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineRecoveryUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelScalarRecovery
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DescentOverlapCharts
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.OrdinaryGlobalLineDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveKernelCharacters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterCorrespondence
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ScalarDescentSymmetry
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTranslations
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfCoverDetection
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HomogeneousCoverCriterion
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitFamilyCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HomogeneousCharacterLines
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterDualPoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterLines
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TensorFrames
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TensorCanonicalDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineProducts
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTorsionFactor
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterGroupPoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterCharacterRestriction
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineFaithfulness
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Rank
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteGroupRankIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DomainRank
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntegralDegree
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IsogenyTorsionRank
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardRankIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RestrictedSheafInjection
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricCharacterMonomorphism
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeTorsionRank
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.WeilPairing
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Polarizations
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Polarized Torsion -/

namespace OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

noncomputable section

/-!
# CartierDuality: Cartier duality and polarized torsion blocks

This file proves both theorems of the CartierDuality schema in actual commutative
fppf sheaves, without importing any statement module:

* `Hodge.CartierDuality.cartier_duality` proves finite locally free
 representability of the actual internal-Hom character sheaf, perfection
 of evaluation, canonical biduality, and arbitrary base change.
* `Hodge.CartierDuality.polarization_blocks_and_annihilators` proves perfection
 on adjoint torsion blocks, finite locally free annihilators, the canonical
 quotient-dual isomorphism, double annihilation, and arbitrary base change.

The geometric interface uses native smooth proper geometrically connected
commutative group schemes and polarizations with their normalized Poincare
representation and actual geometric ampleness. Positive torsion is proved
finite locally free over arbitrary bases, allowing varying relative
dimension and all residue characteristics.

The Weil pairing is constructed from actual line descent. An internal-Hom
character of the multiplication kernel gives an ordinary descent cocycle;
its descended homogeneous line represents a point of the Picard dual.
This construction is natural on every parameter scheme and preserves the
Picard group law. It gives the canonical map from the Cartier dual of
A[n] to the actual dual n-torsion. On geometric fibers this map is monic
on all test schemes, including nonreduced schemes. The finite-flat degree
tower law gives equality of the two torsion ranks across an isogeny.
Geometric fibers then prove the original map is an isomorphism over the
arbitrary base. Its inverse supplies the actual Weil characters.

`Polarization.torsionPairing` applies the polarization's canonical torsion
map in the second variable of this Weil pairing. Its construction uses
only the positive-n hypothesis, passed explicitly as `hn: 0 < n`.
Coprimality with the actual fiber degree is used solely to prove that the
polarization's torsion map is an isomorphism. No invertibility of n on the
base, block representability assumption, or assumed ambient perfection is
required. Actual product decompositions and pointwise adjoint projectors
then give all block and annihilator conclusions.

The final command audits both public theorems and the constructed pairing
against Lean's standard logical axioms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open scoped TensorProduct

universe u

namespace Construction

/-- Commutativity of the affine group object forces cocommutativity of
its coordinate Hopf algebra, tested on the two universal tensor points. -/
theorem cocomm_of_commutative_affineGroup
    (R A : Type u) [CommRing R] [CommRing A] [Bialgebra R A]
    [IsCommMonObj ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)))] :
    Coalgebra.IsCocomm R A := by
  let f : WithConv (A →ₐ[R] A ⊗[R] A) :=
    WithConv.toConv Algebra.TensorProduct.includeLeft
  let g : WithConv (A →ₐ[R] A ⊗[R] A) :=
    WithConv.toConv Algebra.TensorProduct.includeRight
  have hfg : f * g = g * f := by
    apply (Spec.mapMulEquiv (R := R) (S := A) (T := A ⊗[R] A)).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hleft : Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ => .all ..) =
      AlgHom.id R (A ⊗[R] A) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro x y
    simp [f, g]
  have hright : Algebra.TensorProduct.lift g.ofConv f.ofConv (fun _ _ => .all ..) =
      (Algebra.TensorProduct.comm R A A).toAlgHom := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro x y
    simp [f, g]
  constructor
  apply LinearMap.ext
  intro x
  change TensorProduct.comm R A A (Coalgebra.comul x) = Coalgebra.comul x
  have h := congrArg (fun k : WithConv (A →ₐ[R] A ⊗[R] A) => k x) hfg
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, hleft, hright] at h
  exact h.symm

/-- A finite locally free commutative group scheme over an affine base has
the finite projective commutative, cocommutative Hopf presentation required
by the dual construction. -/
theorem exists_finiteProjective_commutative_hopfPresentation
    (R : CommRingCat.{u}) (G : Grp (Over (Spec R))) [IsCommMonObj G.X]
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    ∃ A : CommHopfAlgCat R,
      Module.Finite R A ∧ Module.Projective R A ∧ Coalgebra.IsCocomm R A ∧
        Nonempty ((hopfSpec R).obj (Opposite.op A) ≅ G) := by
  obtain ⟨A, hf, hp, ⟨e⟩⟩ := AbelianScheme.CartierDuality.FiniteLocallyFreeCoordinates.Construction.exists_finiteProjective_hopfPresentation R G
  let i : ((hopfSpec R).obj (Opposite.op A)).X ≅ G.X := (Grp.forget _).mapIso e
  have : IsMonHom i.hom := inferInstanceAs (IsMonHom e.hom.hom.hom)
  have hcomm : IsCommMonObj ((hopfSpec R).obj (Opposite.op A)).X := by
    apply (isCommMonObj_iff_isMulCommutative _).mpr
    intro X
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (cancel_mono i.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    exact mul_comm _ _
  let : IsCommMonObj
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) := hcomm
  exact ⟨A, hf, hp, cocomm_of_commutative_affineGroup R A, ⟨e⟩⟩

variable (R A : Type u) [CommRing R] [CommRing A]
variable [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

/-- The affine group scheme attached to the dual coordinate Hopf algebra. -/
def dualCoordinateScheme : Over (Spec (CommRingCat.of R)) :=
  (Spec (CommRingCat.of (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R))

instance dualCoordinateScheme_group : GrpObj (dualCoordinateScheme R A) := by
  unfold dualCoordinateScheme
  infer_instance

instance dualCoordinateScheme_commutative : IsCommMonObj (dualCoordinateScheme R A) := by
  unfold dualCoordinateScheme
  infer_instance

/-- The constructed dual affine group scheme is finite locally free. -/
theorem dualCoordinateScheme_finiteLocallyFree :
    IsFinite (dualCoordinateScheme R A).hom ∧
    Flat (dualCoordinateScheme R A).hom ∧
    LocallyOfFinitePresentation (dualCoordinateScheme R A).hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A)))) ∧
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A)))) ∧
    LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A))))
  exact (AbelianScheme.CartierDuality.FiniteLocallyFreeCoordinates.Construction.finiteLocallyFree_spec_iff R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A)).mpr
    ⟨inferInstance, inferInstance⟩

/-- The constructed affine group scheme is canonically isomorphic to its
Cartier bidual, via the transpose of evaluation. -/
def dualCoordinateSchemeBidualIso :
    dualCoordinateScheme R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A) ≅
      (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) :=
  (Grp.forget _).mapIso <|
    (hopfSpec (CommRingCat.of R)).mapIso
      (CommHopfAlgCat.isoMk (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A)).op

/-- On every affine test scheme, points of the constructed dual are
exactly group-scheme characters of the base-changed original group.
The tensor product here is the coordinate algebra of the scheme pullback. -/
def affineCartierCharacterEquiv
    (S : Type u) [CommRing S] [Algebra R S] :
    ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)) ⟶
      dualCoordinateScheme R A) ≃
    (AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme S (S ⊗[R] A) ⟶ AbelianScheme.CartierDuality.Characters.Construction.multiplicativeGroupScheme S) :=
  (AbelianScheme.CartierDuality.Characters.Construction.affineSchemePointsEquivAlgHom R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A) S).trans <|
    (AbelianScheme.CartierDuality.DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).trans <|
      AbelianScheme.CartierDuality.Characters.Construction.groupLikeEquivSchemeCharacters S (S ⊗[R] A)

namespace AffineSchemes

variable (R : CommRingCat.{u})

/-- Native geometric hypotheses for a finite locally free commutative
group scheme over an affine base. -/
def finiteLocallyFreeCommGroup : ObjectProperty (Grp (Over (Spec R))) :=
  fun G => IsFinite G.X.hom ∧ Flat G.X.hom ∧
    LocallyOfFinitePresentation G.X.hom ∧ IsCommMonObj G.X

abbrev FiniteLocallyFreeCommGroup := (finiteLocallyFreeCommGroup R).FullSubcategory

instance (G : FiniteLocallyFreeCommGroup R) : IsFinite G.obj.X.hom := G.property.1
instance (G : FiniteLocallyFreeCommGroup R) : Flat G.obj.X.hom := G.property.2.1
instance (G : FiniteLocallyFreeCommGroup R) : LocallyOfFinitePresentation G.obj.X.hom :=
  G.property.2.2.1
instance (G : FiniteLocallyFreeCommGroup R) : IsCommMonObj G.obj.X := G.property.2.2.2

/-- Spectrum takes precisely the relevant Hopf coordinates to native
finite locally free commutative group schemes. -/
def finiteProjectiveHopfSpec :
    (AbelianScheme.CartierDuality.AffineCategory.Construction.FiniteProjectiveHopf R)ᵒᵖ ⥤ FiniteLocallyFreeCommGroup R where
  obj A := ⟨(hopfSpec R).obj (Opposite.op A.unop.obj), by
    have h := (AbelianScheme.CartierDuality.FiniteLocallyFreeCoordinates.Construction.finiteLocallyFree_spec_iff R A.unop.obj).mpr
      ⟨inferInstance, inferInstance⟩
    have hc : IsCommMonObj
        ((Spec (CommRingCat.of A.unop.obj)).asOver (Spec R)) := inferInstance
    exact ⟨h.1, h.2.1, h.2.2, hc⟩⟩
  map f := ObjectProperty.homMk ((hopfSpec R).map f.unop.hom.op)
  map_id A := by
    apply ObjectProperty.hom_ext
    exact (hopfSpec R).map_id (Opposite.op A.unop.obj)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (hopfSpec R).map_comp f.unop.hom.op g.unop.hom.op

def finiteProjectiveHopfSpec_fullyFaithful :
    (finiteProjectiveHopfSpec R).FullyFaithful where
  preimage f := (ObjectProperty.homMk
    ((hopfSpec.fullyFaithful (R := R)).preimage f.hom).unop).op
  map_preimage f := by
    apply ObjectProperty.hom_ext
    exact (hopfSpec.fullyFaithful (R := R)).map_preimage f.hom
  preimage_map f := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact congrArg Quiver.Hom.unop
      ((hopfSpec.fullyFaithful (R := R)).preimage_map f.unop.hom.op)

instance : (finiteProjectiveHopfSpec R).Full := (finiteProjectiveHopfSpec_fullyFaithful R).full
instance : (finiteProjectiveHopfSpec R).Faithful :=
  (finiteProjectiveHopfSpec_fullyFaithful R).faithful

instance : (finiteProjectiveHopfSpec R).EssSurj where
  mem_essImage G := by
    obtain ⟨A, hf, hp, hc, ⟨e⟩⟩ :=
      exists_finiteProjective_commutative_hopfPresentation R G.obj
    exact ⟨Opposite.op ⟨A, hf, hp, hc⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

instance : (finiteProjectiveHopfSpec R).IsEquivalence where

/-- The geometric finite locally free condition is equivalent to the
finite projective Hopf-coordinate condition over any affine base. -/
def finiteProjectiveHopfSpecEquivalence :
    (AbelianScheme.CartierDuality.AffineCategory.Construction.FiniteProjectiveHopf R)ᵒᵖ ≌ FiniteLocallyFreeCommGroup R :=
  (finiteProjectiveHopfSpec R).asEquivalence

/-- The constructed Cartier operation is a contravariant equivalence of
native finite locally free commutative group schemes over an affine base. -/
def affineGroupDualityEquivalence :
    (FiniteLocallyFreeCommGroup R)ᵒᵖ ≌ FiniteLocallyFreeCommGroup R :=
  (finiteProjectiveHopfSpecEquivalence R).symm.leftOp.trans <|
    (AbelianScheme.CartierDuality.AffineCategory.Construction.finiteProjectiveHopfDualEquivalence R).rightOp.trans <|
      finiteProjectiveHopfSpecEquivalence R

end AffineSchemes

/-- Over an affine base, the actual character sheaf of every finite
locally free commutative group scheme is finite locally free representable.
The coordinate Hopf algebra is extracted from the geometric hypotheses. -/
theorem affine_characterSheaf_finiteLocallyFree
    (R : CommRingCat.{u}) (G : Grp (Over (Spec R))) [IsCommMonObj G.X]
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    AbelianScheme.CartierDuality.CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G) := by
  obtain ⟨A, hf, hp, hc, ⟨e⟩⟩ := exists_finiteProjective_commutative_hopfPresentation R G
  let : Module.Finite R A := hf
  let : Module.Projective R A := hp
  let : Coalgebra.IsCocomm R A := hc
  obtain ⟨hfinite, hflat, hfp⟩ := dualCoordinateScheme_finiteLocallyFree R A
  refine ⟨dualCoordinateScheme R A, hfinite, hflat, hfp, ?_⟩
  let i₀ := @asIso _ _ _ _ (AbelianScheme.CartierDuality.CharacterMap.Construction.affineCartierCharacterSheafMap R A)
    (AbelianScheme.CartierDuality.AffineSheafIso.Construction.affineCartierCharacterSheafMap_isIso R A)
  let i : AbelianScheme.CartierDuality.CharacterFunctor.Construction.Schemes.pointSheaf (Spec R) (dualCoordinateScheme R A) ≅
      AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) (AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme R A) :=
    i₀
  exact ⟨i ≪≫ (AbelianScheme.CartierDuality.CharacterFunctor.Construction.Schemes.characterSheafIso e).symm⟩

/-- The affine representability theorem remains valid after an arbitrary,
possibly nonaffine and nonflat, change of base. -/
theorem affine_characterSheaf_baseChange_finiteLocallyFree
    (R : CommRingCat.{u}) (G : Grp (Over (Spec R))) [IsCommMonObj G.X]
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (T : Scheme.{u}) (f : T ⟶ Spec R) :
    AbelianScheme.CartierDuality.CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable
      (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf T ((Over.pullback f).mapGrp.obj G)) :=
  AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.characterRepresentability_baseChange f G (affine_characterSheaf_finiteLocallyFree R G)

/-- The dual Hopf spectrum is a finite locally free commutative group
representative with its canonical character-group isomorphism. -/
def affineCartierGroupRepresentation (R A : Type u) [CommRing R] [CommRing A]
    [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A] :
    AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (CommRingCat.of R)) (AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme R A) where
  dual := AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A)
  commutative := inferInstanceAs (IsCommMonObj (dualCoordinateScheme R A))
  finite := (dualCoordinateScheme_finiteLocallyFree R A).1
  flat := (dualCoordinateScheme_finiteLocallyFree R A).2.1
  finitelyPresented := (dualCoordinateScheme_finiteLocallyFree R A).2.2
  pointsIso := AbelianScheme.CartierDuality.AffineCharacterGroups.Construction.affineCartierGroupPointIso R A

/-- The affine group representative gives the canonical universal
character section on every test scheme. -/
theorem affineCartierGroupRepresentation_section (R A : Type u) [CommRing R] [CommRing A]
    [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A]
    (T : Over (Spec (CommRingCat.of R)))
    (f : T ⟶ (AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A)).X) :
    (affineCartierGroupRepresentation R A).sectionEquiv T f =
      (AbelianScheme.CartierDuality.CharacterMap.Construction.affineCartierCharacterMap R A).app (Opposite.op T) (ULift.up f) :=
  ((affineCartierGroupRepresentation R A).sectionEquiv_apply T f).trans
    (AbelianScheme.CartierDuality.AffineCharacterGroups.Construction.affineCartierGroupPointIso_character R A T f)

/-- On affine test points, evaluation for the canonical affine group
representative is the proved group-like character evaluation. -/
theorem affineCartierGroupRepresentation_evaluation (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R B]
    [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A]
    (p : A →ₐ[R] B) (q : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A →ₐ[R] B) :
    (affineCartierGroupRepresentation R A).evaluationValue
      ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))
      ((AbelianScheme.CartierDuality.Characters.Construction.affineSchemePointsEquivAlgHom R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A) B).symm q)
      ((AbelianScheme.CartierDuality.Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm p) =
    AbelianScheme.CartierDuality.AffineEvaluationInv.Construction.affineCartierPairValue R B A p q := by
  let T := (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R))
  let d := (AbelianScheme.CartierDuality.Characters.Construction.affineSchemePointsEquivAlgHom R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A) B).symm q
  have h₁ := affineCartierGroupRepresentation_section R A T d
  have h₂ := AbelianScheme.CartierDuality.AffineSheafIso.Construction.affineCartierCharacterMap_apply_affine R B A d
  have h₃ := congrArg (fun f => AbelianScheme.CartierDuality.AffineCharacterValues.Construction.affineGroupLikeSection R B A (AbelianScheme.CartierDuality.DualAlgebra.Construction.affineDualPointsEquivCharacters R B A f))
    ((AbelianScheme.CartierDuality.Characters.Construction.affineSchemePointsEquivAlgHom R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A) B).apply_symm_apply q)
  exact (affineCartierGroupRepresentation R A).evaluationValue_of_section_eq T d
    ((AbelianScheme.CartierDuality.Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm p) (h₁.trans (h₂.trans h₃))

/-- Canonical bidual evaluation agrees with the inverse coordinate
bidual isomorphism, as an actual morphism of affine group schemes. -/
theorem affineCartierBidualEvaluation_eq_coordinate (R A : Type u) [CommRing R] [CommRing A]
    [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A] :
    (affineCartierGroupRepresentation R A).bidualEvaluation
      (affineCartierGroupRepresentation R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A)) = (AbelianScheme.CartierDuality.AffineEvaluationInv.Construction.coordinateBidualGroupIso R A).inv := by
  apply AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_eq_of_affine_pairing
    (CommRingCat.of R) (AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme R A)
  intro B x d
  obtain ⟨p, rfl⟩ := (AbelianScheme.CartierDuality.Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm.surjective x
  obtain ⟨q, rfl⟩ := (AbelianScheme.CartierDuality.Characters.Construction.affineSchemePointsEquivAlgHom R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A) B).symm.surjective d
  have hp := AbelianScheme.CartierDuality.AffineEvaluationInv.Construction.coordinateBidualGroupIso_inv_point R B A p
  have he := affineCartierGroupRepresentation_evaluation R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A) B q
    (AbelianScheme.CartierDuality.EvaluationSymmetry.Construction.bidualEvaluationAlgPoint R B A p)
  have hs := AbelianScheme.CartierDuality.AffineEvaluationInv.Construction.affineCharacterEvaluation_value_symmetry R B A p q
  have hd := affineCartierGroupRepresentation_evaluation R A B p q
  have hpoint := congrArg
    (fun y => (affineCartierGroupRepresentation R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A)).evaluationValue
      ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R))) y
        ((AbelianScheme.CartierDuality.Characters.Construction.affineSchemePointsEquivAlgHom R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A) B).symm q)) hp
  have hsd := hs.symm.trans hd.symm
  have hed := he.trans hsd
  have hfinal := hpoint.trans hed
  exact hfinal

/-- The canonical evaluation map to the Cartier bidual is an isomorphism
for finite locally free commutative affine Hopf group schemes. -/
theorem affineCartierBidualEvaluation_isIso (R A : Type u) [CommRing R] [CommRing A]
    [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A] :
    IsIso ((affineCartierGroupRepresentation R A).bidualEvaluation
      (affineCartierGroupRepresentation R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A))) := by
  rw [affineCartierBidualEvaluation_eq_coordinate]
  exact (AbelianScheme.CartierDuality.AffineEvaluationInv.Construction.coordinateBidualGroupIso R A).isIso_inv

/-- Canonical bidual evaluation is perfect for every finite locally
free commutative group scheme over an affine base and every choice
of native first and second character representatives. -/
theorem bidualEvaluation_isIso_affine (R : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (D : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec R) G)
    (E : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec R) D.dual) :
    IsIso (D.bidualEvaluation E) := by
  obtain ⟨A, hf, hp, hc, ⟨e⟩⟩ := exists_finiteProjective_commutative_hopfPresentation R G
  let : Module.Finite R A := hf
  let : Module.Projective R A := hp
  let : Coalgebra.IsCocomm R A := hc
  let D₀ := affineCartierGroupRepresentation R A
  let E₀ := affineCartierGroupRepresentation R (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R A)
  let : IsIso (D₀.bidualEvaluation E₀) := affineCartierBidualEvaluation_isIso R A
  let i : G ≅ AbelianScheme.CartierDuality.Characters.Construction.affineHopfGroupScheme R A := e.symm
  exact D₀.bidualEvaluation_isIso_of_sourceIso D E₀ E i

/-- The actual fppf character sheaf of a finite locally free commutative
group scheme over any base scheme is represented by a finite locally free
scheme. This follows from affine Hopf duality and open-base descent. -/
theorem characterSheaf_finiteLocallyFree (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] :
    AbelianScheme.CartierDuality.CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S G) := by
  apply AbelianScheme.CartierDuality.RepresentabilityDescent.Construction.Schemes.character_finiteLocallyFree_of_openCover G S.affineCover
  intro k
  let G' := (Over.pullback (S.affineCover.f k)).mapGrp.obj G
  let hc : IsCommMonObj G'.X :=
    Functor.isCommMonObj_obj (F := Over.pullback (S.affineCover.f k)) (M := G.X)
  let hf : IsFinite G'.X.hom :=
    inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd G.X.hom (S.affineCover.f k)))
  let hflat : Flat G'.X.hom :=
    inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd G.X.hom (S.affineCover.f k)))
  let hfp : LocallyOfFinitePresentation G'.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation
      (CategoryTheory.Limits.pullback.snd G.X.hom (S.affineCover.f k)))
  exact @affine_characterSheaf_finiteLocallyFree _ G' hc hf hflat hfp

/-- Canonical bidual evaluation is an isomorphism over an arbitrary
base scheme, for every choice of actual character representatives. -/
theorem bidualEvaluation_isIso (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (D : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (E : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) : IsIso (D.bidualEvaluation E) := by
  apply AbelianScheme.CartierDuality.LocalIsomorphismsIs.Construction.Schemes.groupMap_isIso_of_openCover (D.bidualEvaluation E) S.affineCover
  intro k
  let f := S.affineCover.f k
  let G' := (Over.pullback f).mapGrp.obj G
  let hc : IsCommMonObj G'.X := Functor.isCommMonObj_obj (F := Over.pullback f) (M := G.X)
  let hf : IsFinite G'.X.hom :=
    inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd G.X.hom f))
  let hflat : Flat G'.X.hom :=
    inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd G.X.hom f))
  let hfp : LocallyOfFinitePresentation G'.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd G.X.hom f))
  have hb := @bidualEvaluation_isIso_affine _ G' hc hf hflat hfp (D.baseChange f) (E.baseChange f)
  exact (D.bidualEvaluation_baseChange E f) ▸ hb

/-- Cartier duality produces a native finite locally free commutative
group scheme over every base, representing the actual character groups. -/
def cartierDualGroupRepresentation (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G :=
  AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.characterGroupRepresentationOfRepresentable S G (characterSheaf_finiteLocallyFree S G)

/-- The native Cartier-dual group scheme, constructed from the proved
representation of the actual character groups. -/
abbrev cartierDualGroupScheme (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] : Grp (Over S) :=
  (cartierDualGroupRepresentation S G).dual

instance cartierDualGroupScheme_commutative (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] : IsCommMonObj (cartierDualGroupScheme S G).X :=
  (cartierDualGroupRepresentation S G).commutative

instance cartierDualGroupScheme_finite (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] : IsFinite (cartierDualGroupScheme S G).X.hom :=
  (cartierDualGroupRepresentation S G).finite

instance cartierDualGroupScheme_flat (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] : Flat (cartierDualGroupScheme S G).X.hom :=
  (cartierDualGroupRepresentation S G).flat

instance cartierDualGroupScheme_finitelyPresented (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] :
    LocallyOfFinitePresentation (cartierDualGroupScheme S G).X.hom :=
  (cartierDualGroupRepresentation S G).finitelyPresented

/-- Canonical evaluation into the native double Cartier dual over an
arbitrary base scheme. Its character formula is proved in `Evaluation`. -/
def cartierBidualEvaluation (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] :
    G ⟶ cartierDualGroupScheme S (cartierDualGroupScheme S G) :=
  (cartierDualGroupRepresentation S G).bidualEvaluation
    (cartierDualGroupRepresentation S (cartierDualGroupScheme S G))

/-- The chosen global Cartier construction has perfect canonical
bidual evaluation whenever the base is affine. -/
theorem cartierBidualEvaluation_isIso_affine (R : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    IsIso (cartierBidualEvaluation (Spec R) G) :=
  bidualEvaluation_isIso_affine R G (cartierDualGroupRepresentation (Spec R) G)
    (cartierDualGroupRepresentation (Spec R) (cartierDualGroupScheme (Spec R) G))

/-- The canonical evaluation into the double Cartier dual is an
isomorphism over every base scheme. -/
theorem cartierBidualEvaluation_isIso (S : Scheme.{u}) (G : Grp (Over S))
    [IsCommMonObj G.X] [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    IsIso (cartierBidualEvaluation S G) :=
  bidualEvaluation_isIso S G (cartierDualGroupRepresentation S G)
    (cartierDualGroupRepresentation S (cartierDualGroupScheme S G))

/-- Cartier duality for actual finite locally free representable
commutative fppf sheaves: representability, perfect canonical evaluation,
canonical biduality, and arbitrary base change. -/
theorem cartier_duality {S : Scheme.{u}} (F : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S)
    (hF : AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S F) :
    AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf F) ∧
      (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.cartierEvaluationPairing F).IsPerfect ∧
      IsIso (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation F) ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S), IsIso (AbelianScheme.CartierDuality.SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f F).hom) := by
  obtain ⟨G, hc, hf, hflat, hfp, ⟨e⟩⟩ := hF
  let : IsCommMonObj G.X := hc
  let : IsFinite G.X.hom := hf
  let : Flat G.X.hom := hflat
  let : LocallyOfFinitePresentation G.X.hom := hfp
  let D := cartierDualGroupRepresentation S G
  let : IsCommMonObj D.dual.X := D.commutative
  let : IsFinite D.dual.X.hom := D.finite
  let : Flat D.dual.X.hom := D.flat
  let : LocallyOfFinitePresentation D.dual.X.hom := D.finitelyPresented
  let E := cartierDualGroupRepresentation S D.dual
  let hn : IsIso (D.bidualEvaluation E) := bidualEvaluation_isIso S G D E
  let hr : IsIso (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)) :=
    D.sheafBidualEvaluation_isIso E
  have hb : IsIso (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation F) :=
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_isIso_of_iso e.symm
  have hd : AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf F) :=
    D.sheafDual_finiteLocallyFree.of_iso ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso e.symm.op)
  exact ⟨hd, (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.cartierEvaluationPairing_isPerfect_iff F).mpr hb, hb,
    fun T f => (AbelianScheme.CartierDuality.SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f F).isIso_hom⟩

/-- A finite locally free subgroup of a finite locally free group has
a finite locally free annihilator under a perfect pairing. -/
theorem annihilator_finiteLocallyFree {S : Scheme.{u}} {G K : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K) (H : Subobject G) (he : e.IsPerfect)
    (hG : AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S G)
    (hH : AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (H : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S)) :
    AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
  (cartier_duality (AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H)
    (AbelianScheme.CartierDuality.QuotientRepresentability.Construction.Schemes.sheafQuotient_finiteLocallyFree H hG hH)).1.of_iso
      (AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.annihilatorQuotientDualIso e H he).symm

/-- Taking the annihilator twice under a perfect pairing recovers
every finite locally free subgroup of a finite locally free group. -/
theorem annihilator_double {S : Scheme.{u}} {G K : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K) (H : Subobject G) (he : e.IsPerfect)
    (hG : AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S G)
    (hH : AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (H : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S)) :
    AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.flip (AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H) = H := by
  let : IsIso (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H)) :=
    (cartier_duality (AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H)
      (AbelianScheme.CartierDuality.QuotientRepresentability.Construction.Schemes.sheafQuotient_finiteLocallyFree H hG hH)).2.2.1
  exact AbelianScheme.CartierDuality.DoubleAnnihilator.Construction.Schemes.sheafAnnihilator_double e H he

end Construction

section

abbrev FppfAb (S : Scheme.{u}) := AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S

abbrev FiniteLocallyFreeRepresentable {S : Scheme.{u}} (G : FppfAb S) :=
  AbelianScheme.CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S G

abbrev cartierDual {S : Scheme.{u}} (G : FppfAb S) := AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G

abbrev BilinearPairing {S : Scheme.{u}} (G K : FppfAb S) := AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K

abbrev IsPerfectPairing {S : Scheme.{u}} {G K : FppfAb S} (e : BilinearPairing G K) := e.IsPerfect

abbrev ProjectorsAdjoint {S : Scheme.{u}} {G K : FppfAb S} (e : BilinearPairing G K)
    (p : G ⟶ G) (q : K ⟶ K) := AbelianScheme.CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint e p q

abbrev SheafBlockDecomposition {S : Scheme.{u}} (G : FppfAb S) (I : Type u) :=
  AbelianScheme.CartierDuality.SheafBlocks.Construction.Schemes.SheafBlockDecomposition G I

abbrev cartierEvaluation {S : Scheme.{u}} (G : FppfAb S) := AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.cartierEvaluationPairing G

abbrev bidualEvaluation {S : Scheme.{u}} (G : FppfAb S) := AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation G

/-- The canonical character comparison for arbitrary scheme base change. -/
def dualBaseChangeComparison {S T : Scheme.{u}} (f : T ⟶ S) (G : FppfAb S) :
    (AbelianScheme.CartierDuality.SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj (cartierDual G) ⟶
      cartierDual ((AbelianScheme.CartierDuality.SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj G) :=
  (AbelianScheme.CartierDuality.SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f G).hom

abbrev sheafQuotient {S : Scheme.{u}} {G : FppfAb S} (H : Subobject G) :=
  AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H

abbrev annihilator {S : Scheme.{u}} {G K : FppfAb S} (e : BilinearPairing G K) (H : Subobject G) :=
  AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H

abbrev baseChangeSubobject {S T : Scheme.{u}} (f : T ⟶ S) {G : FppfAb S} (H : Subobject G) :=
  AbelianScheme.CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangeSubobject f H

abbrev baseChangePairing {S T : Scheme.{u}} (f : T ⟶ S) {G K : FppfAb S}
    (e : BilinearPairing G K) := AbelianScheme.CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing f e

abbrev annihilatorToQuotientDual {S : Scheme.{u}} {G K : FppfAb S}
    (e : BilinearPairing G K) (H : Subobject G) :=
  AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.annihilatorToQuotientDual e H

/-- The canonical annihilator comparison for any perfect pairing of
commutative fppf sheaves is an isomorphism. -/
theorem annihilatorToQuotientDual_isIso_of_perfect {S : Scheme.{u}} {G K : FppfAb S}
    (e : BilinearPairing G K) (H : Subobject G) (he : IsPerfectPairing e) :
    IsIso (annihilatorToQuotientDual e H) :=
  AbelianScheme.CartierDuality.SheafQuotients.Construction.Schemes.annihilatorToQuotientDual_isIso e H he

/-- Cartier duality for finite locally free commutative group schemes,
expressed in the actual commutative fppf-sheaf interface of the CartierDuality schema. -/
theorem cartier_duality {S : Scheme.{u}} (G : FppfAb S) (hG : FiniteLocallyFreeRepresentable G) :
    FiniteLocallyFreeRepresentable (cartierDual G) ∧
    IsPerfectPairing (cartierEvaluation G) ∧
    IsIso (PolarizedTorsion.bidualEvaluation G) ∧
    (∀ (T : Scheme.{u}) (f : T ⟶ S), IsIso (dualBaseChangeComparison f G)) :=
  Construction.cartier_duality G hG

/-- Annihilator representability, its canonical quotient-dual comparison,
double annihilation, and arbitrary base change for a perfect finite locally free pairing. -/
theorem annihilator_duality {S : Scheme.{u}} {G K : FppfAb S}
    (e : BilinearPairing G K) (H : Subobject G) (he : IsPerfectPairing e)
    (hG : FiniteLocallyFreeRepresentable G)
    (hH : FiniteLocallyFreeRepresentable (H : FppfAb S)) :
    FiniteLocallyFreeRepresentable (annihilator e H : FppfAb S) ∧
      IsIso (annihilatorToQuotientDual e H) ∧
      annihilator e.flip (annihilator e H) = H ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S),
        baseChangeSubobject f (annihilator e H) =
          annihilator (baseChangePairing f e) (baseChangeSubobject f H)) :=
  ⟨Construction.annihilator_finiteLocallyFree e H he hG hH,
    annihilatorToQuotientDual_isIso_of_perfect e H he,
    Construction.annihilator_double e H he hG hH,
    fun _ f => AbelianScheme.CartierDuality.AnnihilatorBaseChange.Construction.Schemes.sheafAnnihilator_baseChange f e H⟩

/-- The sheaf-theoretic block and annihilator conclusions, derived from
an ambient finite locally free group with a perfect pairing and pointwise
adjoint projectors. No block representability is assumed. -/
theorem perfect_pairing_blocks_and_annihilators {S : Scheme.{u}} {G : FppfAb S}
    (hG : FiniteLocallyFreeRepresentable G) (e : BilinearPairing G G) (he : IsPerfectPairing e)
    {I : Type u} (B : SheafBlockDecomposition G I) (i j : I)
    (hadjoint : ProjectorsAdjoint e (B.projector i) (B.projector j))
    (H : Subobject (B.block i)) (hH : FiniteLocallyFreeRepresentable (H : FppfAb S)) :
    let b := B.restrictedPairing e i j
    IsPerfectPairing b ∧
      FiniteLocallyFreeRepresentable (annihilator b H : FppfAb S) ∧
      IsIso (annihilatorToQuotientDual b H) ∧
      annihilator b.flip (annihilator b H) = H ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S),
        baseChangeSubobject f (annihilator b H) =
          annihilator (baseChangePairing f b) (baseChangeSubobject f H)) := by
  have hb := B.restrictedPairing_isPerfect e he i j hadjoint
  exact ⟨hb, annihilator_duality (B.restrictedPairing e i j) H hb
    (B.block_finiteLocallyFree hG i) hH⟩

end

open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

/-- A native smooth proper geometrically connected commutative group scheme. -/
abbrev AbelianScheme (S : Scheme.{u}) := Picard.Homomorphisms.AbelianSchemes.Construction.AbelianScheme S

/-- An actual polarization, with normalized Poincare representation and geometric ampleness. -/
abbrev Polarization {S : Scheme.{u}} (A : AbelianScheme S) := Picard.Homomorphisms.Polarizations.Construction.Polarization A

/-- The actual kernel of multiplication in commutative fppf sheaves. -/
def AbelianScheme.torsionSheaf {S : Scheme.{u}} (A : AbelianScheme S) (n : ℕ) : FppfAb S :=
  AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.toOver)) n

/-- The degree on each fiber, computed from the finite-flat polarization map. -/
def Polarization.fiberDegree {S : Scheme.{u}} {A : AbelianScheme S} (ell : Polarization A) (s : S) : ℕ :=
  ell.map.left.finrank (η[ell.dual.abelian].left s)

/-- The polarization acts on torsion by the canonical morphism of sheaf kernels. -/
def Polarization.torsionMap {S : Scheme.{u}} {A : AbelianScheme S} (ell : Polarization A) (n : ℕ) :
    A.torsionSheaf n ⟶ AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk ell.dual.abelian)) n :=
  AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
    (@Grp.homMk (Over S) _ _ (Grp.mk A.toOver) (Grp.mk ell.dual.abelian) ell.map ell.preservesGroup)) n

/-- Character-line descent identifies the actual Cartier dual of torsion with dual torsion.
The isomorphism exists for every positive n, independently of the polarization degree. -/
def Polarization.torsionCartierIso {S : Scheme.{u}} {A : AbelianScheme S}
    (ell : Polarization A) (n : ℕ) (hn : 0 < n) :
    cartierDual (A.torsionSheaf n) ≅ AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk ell.dual.abelian)) n := by
  have : IsMonHom (show A.toOver ⟶ ell.dual.abelian from ell.map) := ell.preservesGroup
  have : IsFinite (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.finite
  have : Flat (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.flat
  have : Surjective (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.surjective
  have hc := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.toOver ell.dual ell.map n hn
  have : IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hc.1
  have : Flat ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hc.2.2.2
  let K := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n))
  have hK := AbelianScheme.CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A.toOver) n
  have : IsCommMonObj K.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative ((𝟙 A.toOver) ^ n)
  have : IsFinite K.X.hom := hK.1
  have : Flat K.X.hom := hK.2.1
  have : LocallyOfFinitePresentation K.X.hom := hK.2.2
  exact AbelianScheme.CartierDuality.WeilPairing.Construction.KernelCharacters.torsionCartierPicardIso A.toOver ell.representation ell.map n hn
    (Construction.cartierDualGroupRepresentation S K)

/-- The Weil pairing evaluates the character corresponding to the dual point by actual line descent. -/
def Polarization.weilPairing {S : Scheme.{u}} {A : AbelianScheme S}
    (ell : Polarization A) (n : ℕ) (hn : 0 < n) :
    BilinearPairing (A.torsionSheaf n) (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk ell.dual.abelian)) n) :=
  (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk (ell.torsionCartierIso n hn).inv).flip

/-- The induced pairing is the actual Weil pairing with the polarization applied in its second variable. -/
def Polarization.torsionPairing {S : Scheme.{u}} {A : AbelianScheme S}
    (ell : Polarization A) (n : ℕ) (hn : 0 < n) : BilinearPairing (A.torsionSheaf n) (A.torsionSheaf n) :=
  (ell.weilPairing n hn).restrict (𝟙 _) (ell.torsionMap n)

/-- The actual character-line construction determines the Weil character uniquely. -/
theorem Polarization.weilPairing_characterLine {S : Scheme.{u}} {A : AbelianScheme S}
    (ell : Polarization A) (n : ℕ) (hn : 0 < n) :
    (ell.torsionCartierIso n hn).hom ≫ (ell.weilPairing n hn).rightAdjoint = 𝟙 _ := by
  have h : (ell.weilPairing n hn).rightAdjoint = (ell.torsionCartierIso n hn).inv :=
    congrArg AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint
      (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.flip_flip
        (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk (ell.torsionCartierIso n hn).inv))
  rw [h]
  exact (ell.torsionCartierIso n hn).hom_inv_id

/-- Finite local freeness is proved from the abelian scheme and its actual polarization. -/
theorem Polarization.torsion_finiteLocallyFree {S : Scheme.{u}} {A : AbelianScheme S}
    (ell : Polarization A) (n : ℕ) (hn : 0 < n) : FiniteLocallyFreeRepresentable (A.torsionSheaf n) := by
  have : IsMonHom (show A.toOver ⟶ ell.dual.abelian from ell.map) := ell.preservesGroup
  have : IsFinite (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.finite
  exact AbelianScheme.CartierDuality.RelativeTorsion.Construction.RelativeAbelian.torsionFppfAb_finiteLocallyFree A.toOver ell.dual ell.map n hn

/-- Both adjoints of the actual Weil pairing are isomorphisms over every base. -/
theorem Polarization.weilPairing_isPerfect {S : Scheme.{u}} {A : AbelianScheme S}
    (ell : Polarization A) (n : ℕ) (hn : 0 < n) : IsPerfectPairing (ell.weilPairing n hn) := by
  have hb : IsIso (PolarizedTorsion.bidualEvaluation (A.torsionSheaf n)) :=
    (cartier_duality (A.torsionSheaf n) (ell.torsion_finiteLocallyFree n hn)).2.2.1
  constructor
  · exact (@asIso _ _ _ _ (PolarizedTorsion.bidualEvaluation (A.torsionSheaf n)) hb ≪≫
      (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (ell.torsionCartierIso n hn).symm.op).isIso_hom
  · have h : (ell.weilPairing n hn).rightAdjoint = (ell.torsionCartierIso n hn).inv :=
      congrArg AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint
        (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.flip_flip
          (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk (ell.torsionCartierIso n hn).inv))
    rw [h]
    exact (ell.torsionCartierIso n hn).isIso_inv

/-- The degree condition makes the polarization-induced Weil pairing perfect;
there is no restriction on residue characteristic or on specialization. -/
theorem Polarization.torsionPairing_isPerfect {S : Scheme.{u}} {A : AbelianScheme S}
    (ell : Polarization A) (n : ℕ) (hn : 0 < n)
    (hdegree : ∀ s : S, Nat.Coprime n (ell.fiberDegree s)) :
    IsPerfectPairing (ell.torsionPairing n hn) := by
  have : IsMonHom (show A.toOver ⟶ ell.dual.abelian from ell.map) := ell.preservesGroup
  have : IsFinite (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.finite
  have : Flat (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.flat
  have : Surjective (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.surjective
  have hmap : IsIso (ell.torsionMap n) :=
    AbelianScheme.CartierDuality.RelativeTorsion.Construction.RelativeAbelian.torsionSheafMap_isIso A.toOver ell.dual ell.map n hn hdegree
  exact AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.restrict_isPerfect_of_isIso
    (ell.weilPairing n hn) (ell.weilPairing_isPerfect n hn) (𝟙 _) (ell.torsionMap n)

/-- A product decomposition of the actual torsion sheaf, with its actual projectors. -/
abbrev TorsionBlockDecomposition {S : Scheme.{u}} (A : AbelianScheme S) (n : ℕ) (I : Type u) :=
  SheafBlockDecomposition (A.torsionSheaf n) I

/-- Polarization identifies adjoint torsion blocks and determines their actual annihilators,
compatibly with arbitrary base change. All geometric perfection and representability inputs are derived. -/
theorem polarization_blocks_and_annihilators
    {S : Scheme.{u}} (A : AbelianScheme S) (ell : Polarization A)
    (n : ℕ) (hn : 0 < n) (hdegree : ∀ s : S, Nat.Coprime n (ell.fiberDegree s))
    (I : Type u) [Fintype I] (conj : I → I) (_hconj : Function.Involutive conj)
    (B : TorsionBlockDecomposition A n I)
    (hadjoint : ∀ i : I, ProjectorsAdjoint (ell.torsionPairing n hn)
      (B.projector i) (B.projector (conj i)))
    (i : I) (H : Subobject (B.block i)) (hH : FiniteLocallyFreeRepresentable (H : FppfAb S)) :
    let e := B.restrictedPairing (ell.torsionPairing n hn) i (conj i)
    IsPerfectPairing e ∧
      FiniteLocallyFreeRepresentable (annihilator e H : FppfAb S) ∧
      IsIso (annihilatorToQuotientDual e H) ∧
      annihilator e.flip (annihilator e H) = H ∧
      (∀ (T : Scheme.{u}) (f : T ⟶ S),
        baseChangeSubobject f (annihilator e H) =
          annihilator (baseChangePairing f e) (baseChangeSubobject f H)) := by
  exact perfect_pairing_blocks_and_annihilators (ell.torsion_finiteLocallyFree n hn)
    (ell.torsionPairing n hn) (ell.torsionPairing_isPerfect n hn hdegree) B i (conj i)
    (hadjoint i) H hH

end

end OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion
