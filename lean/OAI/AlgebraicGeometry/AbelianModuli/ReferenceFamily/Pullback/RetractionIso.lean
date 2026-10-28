import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Retraction Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.RetractionIso

noncomputable section

/-! The canonical fiber comparison for a retraction of base schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S T : Scheme.{u}}

def pullbackRetractionIso (p : T ⟶ S) (r : S ⟶ T) (w : r ≫ p = 𝟙 S) :
    Over.pullback p ⋙ Over.pullback r ≅ 𝟭 (Over S) :=
  (Over.pullbackComp r p).symm ≪≫
    eqToIso (congrArg (fun f : S ⟶ S => Over.pullback f) w) ≪≫ Over.pullbackId

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.RetractionIso
