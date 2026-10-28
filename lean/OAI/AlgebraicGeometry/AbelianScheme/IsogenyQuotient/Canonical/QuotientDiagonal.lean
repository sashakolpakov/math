import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.CanonicalPoincarePairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PoincareLine
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.DiagonalPositivity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupHomAmpleness

/-! # Quotient Diagonal -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.QuotientDiagonal.Construction

noncomputable section

section

/-! Self-annihilation for the actual canonical CartierDuality pairing supplies
the effective PoincareBundle quotient line of the original Poincare family. The
pairing comparison is proved, so no second isotropy assumption is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)
  {B : Over (Spec (.of k))} [GrpObj B] (f : (A.pullback s).scheme ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator F = F)

include hlag in
theorem canonicalKernel_poincare_selfAnnihilating :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (Geometric.PoincareLine.Construction.geometricPoincareNativeTorsionPairing D pol k s n).relativeAnnihilator F = F := by
  rw [← Geometric.CanonicalPoincarePairing.Construction.geometricCanonicalPolarizationPairing_eq_poincare D pol k s n hn]
  exact hlag

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian (B ⊗ B).left]

def geometricCanonicalQuotientLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ B).left :=
  Geometric.PoincareLine.Construction.geometricPoincareQuotientLine D pol k s n f hker (canonicalKernel_poincare_selfAnnihilating D pol k s n hn f hlag)

def geometricCanonicalQuotientLine_pullbackIso :
    (Scheme.Modules.pullback (f ⊗ₘ f).left).obj
      (geometricCanonicalQuotientLine D pol k s n hn f hker hlag).sheaf ≅
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
      ((Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n)).sheaf :=
  Geometric.PoincareLine.Construction.geometricPoincareQuotientLine_pullbackIso D pol k s n f hker
    (canonicalKernel_poincare_selfAnnihilating D pol k s n hn f hlag)

end

section

/-! The actual diagonal of the quotient line constructed from canonical
self-annihilation pulls back to an ample line. Ampleness descent and an
inducing line for the quotient polarization remain separate obligations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)
  {B : Over (Spec (.of k))} [GrpObj B] (f : (A.pullback s).scheme ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator F = F)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian (B ⊗ B).left]

def geometricCanonicalQuotientDiagonal : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left :=
  (geometricCanonicalQuotientLine D pol k s n hn f hker hlag).pullback (lift (𝟙 B) (𝟙 B)).left

set_option backward.isDefEq.respectTransparency false in
theorem geometricCanonicalQuotientDiagonal_pullback_isAmple :
    ((geometricCanonicalQuotientDiagonal D pol k s n hn f hker hlag).pullback f.left).IsAmple := by
  have : (A.pullback s).scheme.left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (A.pullback s).scheme.hom]
    infer_instance⟩
  obtain ⟨e0⟩ := Picard.PoincareBundle.PolarizationTorsionPairing.inducingLine_zero (D.pullback s) (pol.pullback s)
  obtain ⟨eL⟩ := Picard.PoincareBundle.PolarizationTorsionPairing.inducingLine_formula (D.pullback s) (pol.pullback s)
  exact Picard.PoincareBundle.Pulled.DiagonalPositivity.pullback_isAmple (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s)
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s))
    (Picard.PoincareBundle.PolarizationTorsionPairing.inducingLine (D.pullback s) (pol.pullback s)) (Picard.PoincareBundle.PolarizationTorsionPairing.inducingLine_ample (D.pullback s) (pol.pullback s))
    e0 eL n hn f (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (geometricCanonicalQuotientLine D pol k s n hn f hker hlag))
    (geometricCanonicalQuotientLine_pullbackIso D pol k s n hn f hker hlag)

end

/-! The actual diagonal line on the canonical isotropic quotient is
ample. Connectedness follows from the original abelian variety and
surjectivity, and positivity descends by the constructed norm sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)
  {B : Over (Spec (.of k))} [GrpObj B] (f : (A.pullback s).scheme ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator F = F)
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  [IsLocallyNoetherian (B ⊗ B).left]

theorem geometricCanonicalQuotientDiagonal_isAmple :
    (geometricCanonicalQuotientDiagonal D pol k s n hn f hker hlag).IsAmple := by
  have : ConnectedSpace (A.pullback s).scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (A.pullback s).scheme.hom
  have : ConnectedSpace B.left := f.left.surjective.connectedSpace f.left.continuous
  exact GroupHomAmpleness.Construction.finiteFlat_groupHom_isAmple_of_pullback f
    (geometricCanonicalQuotientDiagonal D pol k s n hn f hker hlag)
    (geometricCanonicalQuotientDiagonal_pullback_isAmple D pol k s n hn f hker hlag)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.QuotientDiagonal.Construction
