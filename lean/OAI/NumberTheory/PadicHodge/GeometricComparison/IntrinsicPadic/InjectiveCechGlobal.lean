import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameCechOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProductPreservation
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionComplexRestriction

/-! # Injective Cech Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal

noncomputable section

/-! The native integral-cover Cech total of original injective open sections
computes the original global bounded crystalline cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

private structure IsoChain (C : Type*) [Category C] where
  X₀ : C
  X₁ : C
  X₂ : C
  X₃ : C
  a : X₀ ≅ X₁
  b : X₁ ≅ X₂
  c : X₂ ≅ X₃

private def IsoChain.compose {C : Type*} [Category C] (chain : IsoChain C) :
    chain.X₀ ≅ chain.X₃ := chain.a ≪≫ chain.b ≪≫ chain.c

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

local instance coefficientRing : Ring Rcoeff := (inferInstance : CommRing Rcoeff).toRing

local notation "coverOpens" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "special" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def specialCover : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X → Y.left.Opens :=
  (special).obj ∘ coverOpens

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem cover : iSup (specialCover p X Y f) = ⊤ := by
  apply top_unique
  intro y _
  have hy : f y ∈ ⨆ i, Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i := by
    rw [Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

local instance tuple_preserves (m : ℕ) (t : Fin (m + 1) → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    PreservesLimit (Discrete.functor (coverOpens ∘ t)) special := by
  dsimp only [SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens]
  infer_instance

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

private def restrictionBicomplexIso :=
  ((IntegralComparison.NonemptyCechNerve.complexFunctor coverOpens).mapHomologicalComplex (.up ℕ)).mapIso
    (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f n J)

private def productBicomplexIso :=
  NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso (A := ModuleCat.{2} Rcoeff) special coverOpens
    (IntegralComparison.BoundedOpen.SectionComplex.complex wittMap n J)

private def flasqueBicomplexIso :=
  ((IntegralComparison.NonemptyCechNerve.complexFunctor (specialCover p X Y f)).mapHomologicalComplex (.up ℕ)).mapIso
    (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso wittMap n J).symm

private def isoSource {C : Type*} [Category C] {A B : C} (_e : A ≅ B) : C := A
private def isoTarget {C : Type*} [Category C] {A B : C} (_e : A ≅ B) : C := B

private def alignedRestriction :
    (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} Rcoeff (IntegralComparison.NonemptyCechNerve.nerve coverOpens)).obj
      (((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n).mapHomologicalComplex (.up ℕ)).obj J.cocomplex) ≅ isoTarget (restrictionBicomplexIso p X Y f n J) :=
  restrictionBicomplexIso p X Y f n J

private def alignedProduct :
    isoTarget (restrictionBicomplexIso p X Y f n J) ≅
      isoSource (flasqueBicomplexIso p X Y f n J) :=
  productBicomplexIso p X Y f n J

private def alignedFlasque :
    isoSource (flasqueBicomplexIso p X Y f n J) ≅
    FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex.{1, 0, 2} Rcoeff Y.left.carrier (specialCover p X Y f)
      (IntegralComparison.BoundedOpen.FlasqueComplex.complex wittMap n J) :=
  flasqueBicomplexIso p X Y f n J

private def comparisonChain : IsoChain
    (CochainComplex (CochainComplex (ModuleCat.{2} Rcoeff) ℕ) ℕ) where
  X₀ := _
  X₁ := _
  X₂ := _
  X₃ := _
  a := alignedRestriction p X Y f n J
  b := alignedProduct p X Y f n J
  c := alignedFlasque p X Y f n J

def bicomplexIso :
    (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} Rcoeff (IntegralComparison.NonemptyCechNerve.nerve coverOpens)).obj
      (((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n).mapHomologicalComplex (.up ℕ)).obj J.cocomplex) ≅
    FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex.{1, 0, 2} Rcoeff Y.left.carrier (specialCover p X Y f)
      (IntegralComparison.BoundedOpen.FlasqueComplex.complex wittMap n J) :=
  (IsoChain.compose (comparisonChain p X Y f n J))

def homologyIso (i : ℕ) :
    (((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} Rcoeff (IntegralComparison.NonemptyCechNerve.nerve coverOpens)).obj
      (((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)).total
        (.up ℕ)).homology i ≅
    ModuleCat.of Rcoeff (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso
    (HomologicalComplex₂.total.mapIso (bicomplexIso p X Y f n J) (.up ℕ)) ≪≫
      Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso wittMap n J (specialCover p X Y f)
        (cover p X Y f) i

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal
