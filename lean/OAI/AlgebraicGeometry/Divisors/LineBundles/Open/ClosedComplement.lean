import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Closed Complement -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ClosedComplement.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual reduced closed complement of an open immersion -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem closedImmersion_isNoetherian {Z X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] : AlgebraicGeometry.IsNoetherian Z := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  exact ⟨⟩

variable {U X : Scheme.{0}} (i : U ⟶ X) [IsOpenImmersion i]

def openComplementIdeal : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨(Set.range i)ᶜ, i.isOpenEmbedding.isOpen_range.isClosed_compl⟩

def openComplementScheme : Scheme := (openComplementIdeal i).subscheme

def openComplementInclusion : openComplementScheme i ⟶ X := (openComplementIdeal i).subschemeι

instance openComplementInclusion_isClosedImmersion : IsClosedImmersion (openComplementInclusion i) :=
  inferInstanceAs (IsClosedImmersion (openComplementIdeal i).subschemeι)

theorem openComplementInclusion_range : Set.range (openComplementInclusion i) = (Set.range i)ᶜ := by
  change Set.range (openComplementIdeal i).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, openComplementIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

instance openComplementScheme_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (openComplementScheme i) :=
  closedImmersion_isNoetherian (openComplementInclusion i)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ClosedComplement.BundleCycles
