import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.ConnectedOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.OpenGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineGluing

/-! # Connected Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ConnectedOpen

noncomputable section

/-! A pointed smooth projective family over a locally Noetherian scheme has an open subset classifying precisely its geometrically connected base changes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem pointedSmoothProjective_connected_open
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : Over S} [Smooth X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X) (x : S ⟶ X.left) (hx : x ≫ X.hom = 𝟙 S) :
    ∃ U : S.Opens, ∀ (T : Scheme.{u}) (c : T ⟶ S),
      GeometricallyConnected (pullback.snd X.hom c) ↔ Set.range c ⊆ (U : Set S) := by
  apply Connected.OpenGluing.geometricallyConnected_open_glue X.hom S.affineOpenCover.openCover
  intro i
  let : IsNoetherianRing (S.affineOpenCover.X i) := Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian S i
  let c := S.affineOpenCover.f i
  let Y := (Over.pullback c).obj X
  have : Smooth Y.hom := inferInstanceAs (Smooth (pullback.snd X.hom c))
  exact AffineProjective.ConnectedOpen.pointedSmoothAffineProjective_connected_open (R := S.affineOpenCover.X i) (P.baseChange c)
    (PointedFamilyFiberConnectedness.schemeSectionBaseChange X.hom x hx c) (PointedFamilyFiberConnectedness.schemeSectionBaseChange_section X.hom x hx c)

def pointedProjectiveConnectedOpen
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : Over S} [Smooth X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X) (x : S ⟶ X.left) (hx : x ≫ X.hom = 𝟙 S) : S.Opens :=
  (pointedSmoothProjective_connected_open P x hx).choose

theorem pointedProjectiveConnectedOpen_classifies
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : Over S} [Smooth X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X) (x : S ⟶ X.left) (hx : x ≫ X.hom = 𝟙 S)
    {T : Scheme.{u}} (c : T ⟶ S) :
    GeometricallyConnected (pullback.snd X.hom c) ↔
      Set.range c ⊆ (pointedProjectiveConnectedOpen P x hx : Set S) :=
  (pointedSmoothProjective_connected_open P x hx).choose_spec T c

theorem pointedProjectiveConnectedOpen_connected
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : Over S} [Smooth X.hom]
    (P : ProjectivePresentations.ProjectivePresentation X) (x : S ⟶ X.left) (hx : x ≫ X.hom = 𝟙 S) :
    GeometricallyConnected (pullback.snd X.hom (pointedProjectiveConnectedOpen P x hx).ι) :=
  (pointedProjectiveConnectedOpen_classifies P x hx _).mpr
    (by rw [Scheme.Opens.range_ι])

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ConnectedOpen
