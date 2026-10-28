import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.BaseChangeFunctionSheaf
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFunctions

/-! # Universal Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.UniversalFunctions.Construction

noncomputable section

/-! An abelian family over a locally Noetherian base has the original
base functions after every base change, including non-Noetherian tests.
This property also passes to its actual finite-flat quotients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem noetherianAbelian_hasUniversalGlobalFunctions
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme := by
  intro T b
  exact AbelianModuli.ReferenceFamily.Abelian.BaseChangeFunctionSheaf.abelian_baseChange_globalFunctions_isIso A (pullback.fst A.scheme.hom b)
    (pullback.snd A.scheme.hom b) b (.of_hasPullback A.scheme.hom b)

theorem noetherianAbelian_quotient_hasUniversalGlobalFunctions
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) : GlobalFunctions.Construction.HasUniversalGlobalFunctions B.scheme :=
  GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source f.hom (noetherianAbelian_hasUniversalGlobalFunctions A)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.UniversalFunctions.Construction
