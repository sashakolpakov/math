import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleHomDerivation
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Etale Algebra Derivation Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleAlgebraDerivationFunctor

noncomputable section

/-! Derivations on an etale algebra diagram form a module diagram
with the uniquely constructed etale restriction maps. -/

open _root_.CategoryTheory

variable (k : Type) [CommRing k] {J : Type} [Category J]
    (F : J ⥤ CommAlgCat k)
    (hF : ∀ {i j : J} (f : i ⟶ j), (F.map f).hom.toRingHom.Etale)

def etaleAlgebraDerivationFunctor : J ⥤ ModuleCat k where
  obj i := ModuleCat.of k (Derivation k (F.obj i) (F.obj i))
  map f := ModuleCat.ofHom (EtaleHomDerivation.etaleAlgHomDerivationLinear (F.map f).hom (hF f))
  map_id i := by
    apply ModuleCat.hom_ext
    have hq : (F.map (𝟙 i)).hom = AlgHom.id k (F.obj i) :=
      congrArg (fun f : F.obj i ⟶ F.obj i => f.hom) (F.map_id i)
    have he : (AlgHom.id k (F.obj i)).toRingHom.Etale := hq ▸ hF (𝟙 i)
    exact (EtaleHomDerivation.etaleAlgHomDerivationLinear_congr _ _ (hF (𝟙 i)) he hq).trans
      (EtaleHomDerivation.etaleAlgHomDerivationLinear_id he)
  map_comp f g := by
    apply ModuleCat.hom_ext
    have hq : (F.map (f ≫ g)).hom = (F.map g).hom.comp (F.map f).hom :=
      congrArg (fun h => h.hom) (F.map_comp f g)
    have he : ((F.map g).hom.comp (F.map f).hom).toRingHom.Etale := hq ▸ hF (f ≫ g)
    exact (EtaleHomDerivation.etaleAlgHomDerivationLinear_congr _ _ (hF (f ≫ g)) he hq).trans
      (EtaleHomDerivation.etaleAlgHomDerivationLinear_comp (F.map f).hom (F.map g).hom (hF f) (hF g) he)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleAlgebraDerivationFunctor
