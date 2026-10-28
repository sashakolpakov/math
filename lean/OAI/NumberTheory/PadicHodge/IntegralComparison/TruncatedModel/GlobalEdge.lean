import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CechConeGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation

/-! # Global Edge -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.InjectiveCech

/-! The native integral-cover Cech total of original injective open sections
computes the original global bounded crystalline cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "coverOpens" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "special" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.specialOpens p k n X Y f
local notation "baseMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y

def specialCover : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X → Y.left.Opens :=
  (special).obj ∘ coverOpens

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
omit [Fintype k] [CharP k p] in
theorem cover : iSup (specialCover p k n X Y f) = ⊤ := by
  apply top_unique
  intro y _
  have hy : f y ∈ ⨆ i, (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X i).val := by
    rw [AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

local instance tuple_preserves (m : ℕ) (t : Fin (m + 1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) :
    PreservesLimit (Discrete.functor (coverOpens ∘ t)) special := by
  exact AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.composite_preserves X.left Y.left f (coverOpens ∘ t)

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def homologyIso (i : ℕ) :=
  GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.homologyIso baseMap n J special coverOpens
    (cover p k n X Y f) i

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.InjectiveCech

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge

/-! The canonical global-section edge identifies the original model Cech comparison in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.specialOpens p k n X Y f
local instance tuple_preserves (m : ℕ) (t : Fin (m + 1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) :
    PreservesLimit (Discrete.functor (U ∘ t)) F :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.composite_preserves X.left Y.left f (U ∘ t)

def edge := GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.map w n I F U

omit [Fintype k] [IsSeparated Y.hom] in
theorem quasiIso : QuasiIso (edge p k n X Y f I) :=
  GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.quasiIso w n I F U (InjectiveCech.cover p k n X Y f)

omit [Fintype k] [IsSeparated Y.hom] in
theorem homology (q : ℕ) : HomologicalComplex.homologyMap (edge p k n X Y f I) q ≫
    (InjectiveCech.homologyIso p k n X Y f I q).hom =
      (BoundedOpen.SectionGlobal.homologyIso w n I q).hom :=
  GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.homology w n I F U
    (InjectiveCech.cover p k n X Y f) q

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge

end

end OAI
