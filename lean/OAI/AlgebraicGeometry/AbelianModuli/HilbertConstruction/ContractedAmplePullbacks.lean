import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AmpleTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Contracted Ample Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContractedAmplePullbacks

noncomputable section

/-! A proper reduced connected test scheme mapped affinely into an ample pullback cannot be contracted unless it is a point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}}
variable (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsReduced X] [ConnectedSpace X]
variable (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)

def contractedBundlePullbackIso (f : Y ⟶ Z) (u : X ⟶ Y) (a : Spec (.of K) ⟶ Z)
    (h : u ≫ f = p ≫ a) (L : Line.Bundles.LineBundle Z) :
    ((L.pullback f).pullback u).sheaf ≅ Line.Bundles.structureModule X :=
  (Scheme.Modules.pullbackComp u f).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp p a).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback p).mapIso (L.pullback a).trivialization_of_subsingleton ≪≫
    Line.Bundles.structureModulePullbackIso p

include x hx in
theorem contracted_ample_pullback_isIso (f : Y ⟶ Z) (u : X ⟶ Y) [IsAffineHom u]
    (a : Spec (.of K) ⟶ Z) (h : u ≫ f = p ≫ a) (L : Line.Bundles.LineBundle Z)
    (hL : (L.pullback f).IsAmple) : IsIso p :=
  Proper.AmpleTriviality.properPointed_trivialAmple_isIso p x hx
    ((hL.pullback_of_isAffineHom u).of_iso (contractedBundlePullbackIso p f u a h L))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContractedAmplePullbacks
