import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELProjectiveCover
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.UniversalFunctions
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.FaithfullyFlatDescent

/-! # Fine PEL Universal Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELUniversalFunctions.Construction

noncomputable section

/-! The original unrestricted fine PEL universal abelian family has
universal global functions. ReferenceFamily's projective components give a genuine
complex scheme cover, and the property descends to the original base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false in
theorem finePEL_universal_hasUniversalGlobalFunctions
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)
    (κ : K →+* ℂ) (hC : Z.HasProjectiveBallComponents κ) :
    GlobalFunctions.Construction.HasUniversalGlobalFunctions Z.universal.polarized.abelian.scheme := by
  let A := Z.universal.polarized.abelian
  let u := Spec.map (CommRingCat.ofHom κ)
  let v := pullback.fst Z.space.hom u
  have : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  have : IsLocallyNoetherian (Z.complexFiber κ).left :=
    FinePELProjectiveCover.Construction.finePEL_complex_locallyNoetherian_of_projective_components Z hZ κ hC
  have : IsLocallyNoetherian (pullback Z.space.hom u) :=
    inferInstanceAs (IsLocallyNoetherian (Z.complexFiber κ).left)
  exact GlobalFunctions.Construction.HasUniversalGlobalFunctions.of_faithfullyFlat_baseChange η[A.scheme].left η[A.scheme].w v
    (Noetherian.UniversalFunctions.Construction.noetherianAbelian_hasUniversalGlobalFunctions (A.pullback v))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELUniversalFunctions.Construction
