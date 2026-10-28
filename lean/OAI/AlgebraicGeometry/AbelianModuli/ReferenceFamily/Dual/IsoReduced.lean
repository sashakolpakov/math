import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualOpenFactorization
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Iso Reduced -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.IsoReduced

noncomputable section

section

/-! An isomorphism on the actual special fiber gives a bijection on
the underlying spaces. A morphism that is locally an open immersion is
then an isomorphism, with no assumed global product identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] {X Y : Over (Spec (.of (DualNumber k)))}
    (f : X ⟶ Y) [IsIso ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f)]

theorem dualMorphism_bijective_of_reductionIso : Function.Bijective f.left := by
  let g := (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f
  have : IsIso g.left := (Over.forget _).map_isIso g
  have hg : Function.Bijective g.left := g.left.homeomorph.bijective
  have hx : Function.Bijective (VaryingDualReduction.dualFamilyReduction k X) := (VaryingDualReduction.dualFamilyReductionHomeomorph k X).bijective
  have hy : Function.Bijective (VaryingDualReduction.dualFamilyReduction k Y) := (VaryingDualReduction.dualFamilyReductionHomeomorph k Y).bijective
  have hn (z : ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X).left) :
      f.left (VaryingDualReduction.dualFamilyReduction k X z) = VaryingDualReduction.dualFamilyReduction k Y (g.left z) :=
    congrArg (fun m => m z) (VaryingDualOpenFactorization.dualFamilyReduction_natural k f)
  constructor
  · intro x y hxy
    obtain ⟨x₀, rfl⟩ := hx.surjective x
    obtain ⟨y₀, rfl⟩ := hx.surjective y
    exact congrArg (VaryingDualReduction.dualFamilyReduction k X)
      (hg.injective (hy.injective ((hn x₀).symm.trans (hxy.trans (hn y₀)))))
  · intro y
    obtain ⟨y₀, rfl⟩ := hy.surjective y
    obtain ⟨x₀, hx₀⟩ := hg.surjective y₀
    exact ⟨VaryingDualReduction.dualFamilyReduction k X x₀, (hn x₀).trans (congrArg (VaryingDualReduction.dualFamilyReduction k Y) hx₀)⟩

theorem dualMorphism_left_isIso_of_openCharts (U : X.left.OpenCover)
    (hU : ∀ i : U.I₀, IsOpenImmersion (U.f i ≫ f.left)) : IsIso f.left := by
  have hb := dualMorphism_bijective_of_reductionIso k f
  have : IsOpenImmersion f.left := IsOpenImmersion.of_openCover_source f.left U hb.injective hU
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top f.left
  apply TopologicalSpace.Opens.ext
  exact Set.range_eq_univ.mpr hb.surjective

end

section

/-! An actual map between varying families, with an isomorphism on
the actual special fibers and open local charts, constructs an isomorphism
over the original base with that exact underlying map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] {X Y : Over (Spec (.of (DualNumber k)))} (f : X ⟶ Y)
    (hred : IsIso ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f))
    (U : X.left.OpenCover) (hU : ∀ i : U.I₀, IsOpenImmersion (U.f i ≫ f.left))

def dualIsoOfReducedIsoOpenCharts : X ≅ Y := by
  have : IsIso f.left := @dualMorphism_left_isIso_of_openCharts k inferInstance X Y f hred U hU
  exact Over.isoMk (asIso f.left) f.w

theorem dualIsoOfReducedIsoOpenCharts_hom : (dualIsoOfReducedIsoOpenCharts k f hred U hU).hom = f := by
  apply Over.OverMorphism.ext
  rfl

end

/-! Specialize the actual two-family isomorphism constructor to a
product target, retaining the explicit isomorphism on special fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    (f : X ⟶ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (hred : IsIso ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f))
    (U : X.left.OpenCover) (hU : ∀ i : U.I₀, IsOpenImmersion (U.f i ≫ f.left))

def dualProductIsoWithReducedIso : X ≅
    (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X) :=
  dualIsoOfReducedIsoOpenCharts k (X := X)
    (Y := (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X)) f hred U hU

theorem dualProductIsoWithReducedIso_hom : (dualProductIsoWithReducedIso k X f hred U hU).hom = f :=
  dualIsoOfReducedIsoOpenCharts_hom k (X := X)
    (Y := (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X)) f hred U hU

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.IsoReduced
