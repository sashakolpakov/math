import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory

/-! # Sheafification Monoids -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafificationMonoids

noncomputable section

/-! Set-valued sheafification carries actual commutative monoid objects and their homomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v u w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J (Type w)]

instance sheafificationMonoidal : (sheafification J (Type w)).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

instance sheafificationBraided : (sheafification J (Type w)).Braided :=
  Functor.Braided.ofChosenFiniteProducts _

instance sheafifyMonObj (F : Cᵒᵖ ⥤ Type w) [MonObj F] : MonObj (sheafify J F) :=
  Functor.monObjObj (F := sheafification J (Type w)) F

instance sheafifyIsCommMonObj (F : Cᵒᵖ ⥤ Type w) [MonObj F] [IsCommMonObj F] :
    IsCommMonObj (sheafify J F) :=
  Functor.isCommMonObj_obj (F := sheafification J (Type w))

instance toSheafifyIsMonHom (F : Cᵒᵖ ⥤ Type w) [MonObj F] : IsMonHom (toSheafify J F) := by
  exact ((Functor.mapMonNatTrans (toSheafification J (Type w))).app (Mon.mk F)).isMonHom_hom

instance sheafifyMapIsMonHom {F G : Cᵒᵖ ⥤ Type w} [MonObj F] [MonObj G]
    (a : F ⟶ G) [IsMonHom a] : IsMonHom (sheafifyMap J a) :=
  Functor.map.instIsMonHom (F := sheafification J (Type w)) F G a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafificationMonoids
