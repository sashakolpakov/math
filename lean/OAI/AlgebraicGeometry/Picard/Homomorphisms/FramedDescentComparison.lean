import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentScalars

/-! # Framed Descent Comparison -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentComparison

noncomputable section

/-! Equal framed descent scalars give an isomorphism respecting the
original module-sheaf gluing maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem conjugate_eq_implies_compatible {C : Type*} [Category C]
    {M₁ M₂ N₁ N₂ U : C} (a : M₁ ⟶ M₂) (b : N₁ ⟶ N₂)
    (e₁ : M₁ ≅ U) (e₂ : M₂ ≅ U) (d₁ : N₁ ≅ U) (d₂ : N₂ ≅ U)
    (h : e₁.inv ≫ a ≫ e₂.hom = d₁.inv ≫ b ≫ d₂.hom) :
    (e₁.hom ≫ d₁.inv) ≫ b = a ≫ (e₂.hom ≫ d₂.inv) := by
  have he := congrArg (fun t : End U => e₁.hom ≫ t ≫ d₂.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using he.symm

variable {X : Scheme.{u}} {L M : X.Modules}

theorem pulledModuleFrame_comparison (e : L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (d : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    {T : Scheme.{u}} (x : T ⟶ X) :
    (Scheme.Modules.pullback x).map (e.hom ≫ d.inv) =
      (FramedDescentScalars.Construction.pulledModuleFrame e x).hom ≫ (FramedDescentScalars.Construction.pulledModuleFrame d x).inv := by
  simp only [FramedDescentScalars.Construction.pulledModuleFrame, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

variable {Y : Scheme.{u}} {f : X ⟶ Y} (D E : IntrinsicModuleDescent.Construction.NativeModuleDescent f)
variable (e : D.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (d : E.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

theorem framedDescentScalar_eq_implies_compatible
    {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (h : FramedDescentScalars.Construction.framedDescentScalar D e q x y hx hy = FramedDescentScalars.Construction.framedDescentScalar E d q x y hx hy) :
    (Scheme.Modules.pullback x).map (e.hom ≫ d.inv) ≫ E.hom q x y hx hy =
      D.hom q x y hx hy ≫ (Scheme.Modules.pullback y).map (e.hom ≫ d.inv) := by
  have he : FramedDescentScalars.Construction.framedDescentEnd D e q x y hx hy = FramedDescentScalars.Construction.framedDescentEnd E d q x y hx hy :=
    AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective T h
  rw [pulledModuleFrame_comparison, pulledModuleFrame_comparison]
  exact conjugate_eq_implies_compatible _ _ _ _ _ _ he

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentComparison
