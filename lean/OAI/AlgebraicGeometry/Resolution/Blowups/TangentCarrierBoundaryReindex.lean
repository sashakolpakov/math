import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruentMaps

/-! # Tangent Carrier Boundary Reindex -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierBoundaryReindex.Construction

noncomputable section

section

/-! Concrete initial comparison maps for two local maximal-contact carriers at one order point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure TangentCarrierComparisonAt
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H H' : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) (n : ℕ) (x : X) where
  ambient : Scheme
  left : ambient ⟶ X
  right : ambient ⟶ X
  left_etale : Etale left
  right_etale : Etale right
  ground : left ≫ f = right ≫ f
  ideal : J.comap left = J.comap right
  carrier : H.comap left = H'.comap right
  boundary : ∀ l, (D l).comap left = (D l).comap right
  congruence : IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent left right (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)
  point : ambient
  point_eq : left point = x

attribute [instance] TangentCarrierComparisonAt.left_etale TangentCarrierComparisonAt.right_etale

end

/-! Initial carrier comparisons retain any named family drawn from their fixed boundary labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def TangentCarrierComparisonAt.reindex
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J H H' : X.IdealSheafData}
    {β γ : Type} {D : β → X.IdealSheafData} {n : ℕ} {x : X}
    (A : TangentCarrierComparisonAt f J H H' D n x) (e : γ → β) :
    TangentCarrierComparisonAt f J H H' (fun l => D (e l)) n x where
  ambient := A.ambient
  left := A.left
  right := A.right
  left_etale := A.left_etale
  right_etale := A.right_etale
  ground := A.ground
  ideal := A.ideal
  carrier := A.carrier
  boundary := fun l => A.boundary (e l)
  congruence := A.congruence
  point := A.point
  point_eq := A.point_eq

def TangentCarrierComparisonAt.extendUnitLabels
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J H H' : X.IdealSheafData}
    {β γ : Type} {D : β → X.IdealSheafData} {n : ℕ} {x : X}
    (A : TangentCarrierComparisonAt f J H H' D n x) (e : γ → Option β) :
    TangentCarrierComparisonAt f J H H' (fun l => match e l with | none => ⊤ | some i => D i) n x where
  ambient := A.ambient
  left := A.left
  right := A.right
  left_etale := A.left_etale
  right_etale := A.right_etale
  ground := A.ground
  ideal := A.ideal
  carrier := A.carrier
  boundary := by
    intro l
    cases he : e l with
    | none => simp only [Scheme.IdealSheafData.comap_top]
    | some i => simpa only [he] using A.boundary i
  congruence := A.congruence
  point := A.point
  point_eq := A.point_eq

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierBoundaryReindex.Construction
