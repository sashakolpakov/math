import OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionCurrying
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionPresheaf

/-! # Pairing Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PairingSections

noncomputable section

/-!
# IntegralComparison: incidence pairings give morphisms to the actual incoming-section presheaf
-/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodPairing

universe u v w

variable {C : Type u} [Category.{v} C] {A : Type w} [SemilatticeInf A]
  (R : Type u) [CommRing R] (P : A → ObjectProperty C) (hP : Monotone P)
  (hIncoming : ∀ V {T U : C}, (T ⟶ U) → P V U → P V T)
  (F : Aᵒᵖ ⥤ ModuleCat.{u} R) (G : Cᵒᵖ ⥤ ModuleCat.{u} R)

def family (a : NeighborhoodPairing.Pairing P hIncoming F G) (V : A) :
    (Functor.const (P V).FullSubcategoryᵒᵖ).obj (F.obj (op V)) ⟶ (P V).ι.op ⋙ G where
  app T := a.app T.unop.obj ⟨V, T.unop.property⟩
  naturality T _ α := (Category.id_comp _).trans (a.site α.unop.hom ⟨V, T.unop.property⟩).symm

def toSections (a : NeighborhoodPairing.Pairing P hIncoming F G) :
    F ⟶ Incoming.SectionPresheaf.presheaf R (ModuleCat.of R R) P hP G where
  app V := SectionCurrying.curry R (F.obj V) ((P V.unop).ι.op ⋙ G) (family R P hIncoming F G a V.unop)
  naturality V W α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply NatTrans.ext
    funext T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change a.app T.unop.obj ⟨W.unop, T.unop.property⟩ (r • F.map α x) =
      a.app T.unop.obj ⟨V.unop, hP α.unop.le T.unop.obj T.unop.property⟩ (r • x)
    rw [← (F.map α).hom.map_smul]
    let V₀ : Incoming.Neighborhoods.Objects P T.unop.obj := ⟨W.unop, T.unop.property⟩
    let V₁ : Incoming.Neighborhoods.Objects P T.unop.obj := ⟨V.unop, hP α.unop.le T.unop.obj T.unop.property⟩
    let γ : V₀ ⟶ V₁ := ObjectProperty.homMk α.unop
    exact congrArg (fun f : F.obj V ⟶ G.obj (op T.unop.obj) => f (r • x))
      (a.neighborhood γ)

def fromSections (η : F ⟶ Incoming.SectionPresheaf.presheaf R (ModuleCat.of R R) P hP G) :
    NeighborhoodPairing.Pairing P hIncoming F G where
  app T V := (SectionCurrying.uncurry R (F.obj (op V.obj)) ((P V.obj).ι.op ⋙ G)
    (η.app (op V.obj))).app (op ⟨T, V.property⟩)
  neighborhood := by
    intro T V W α
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : F.obj (op W.obj) ⟶
      ModuleCat.of R (Incoming.SectionRestriction.Sections R (ModuleCat.of R R) (P V.obj) G) =>
        (f x).app (op ⟨T, V.property⟩) (1 : R)) (η.naturality ((Incoming.Neighborhoods.inclusion P T).map α).op)
  site := by
    intro T U α V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (congrArg (fun f : ModuleCat.of R R ⟶ G.obj (op T) => f (1 : R))
      ((η.app (op V.obj) x).naturality
        (ObjectProperty.homMk (X := ⟨T, hIncoming V.obj α V.property⟩)
          (Y := ⟨U, V.property⟩) α).op)).symm

theorem fromSections_toSections (a : NeighborhoodPairing.Pairing P hIncoming F G) :
    fromSections R P hP hIncoming F G (toSections R P hP hIncoming F G a) = a := by
  apply NeighborhoodPairing.Pairing.ext
  funext T V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change a.app T V ((1 : R) • x) = a.app T V x
  rw [one_smul]

theorem toSections_fromSections
    (η : F ⟶ Incoming.SectionPresheaf.presheaf R (ModuleCat.of R R) P hP G) :
    toSections R P hP hIncoming F G (fromSections R P hP hIncoming F G η) = η := by
  apply NatTrans.ext
  funext V
  exact SectionCurrying.curry_uncurry R (F.obj V) ((P V.unop).ι.op ⋙ G) (η.app V)

def equiv : NeighborhoodPairing.Pairing P hIncoming F G ≃
    (F ⟶ Incoming.SectionPresheaf.presheaf R (ModuleCat.of R R) P hP G) where
  toFun := toSections R P hP hIncoming F G
  invFun := fromSections R P hP hIncoming F G
  left_inv := fromSections_toSections R P hP hIncoming F G
  right_inv := toSections_fromSections R P hP hIncoming F G

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PairingSections
