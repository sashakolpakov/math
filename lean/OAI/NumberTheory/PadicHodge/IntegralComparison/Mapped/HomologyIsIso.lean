import Mathlib.Algebra.Homology.Functor

/-! # Homology Is Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.HomologyIsIso

noncomputable section

/-! An exact functor detects invertibility of the homology map of its image. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
  (φ : K ⟶ L) (i : ι)

theorem of_quasiIsoAt [QuasiIsoAt ((F.mapHomologicalComplex c).map φ) i] :
    IsIso (F.map (HomologicalComplex.homologyMap φ i)) := by
  let ψ : K.sc i ⟶ L.sc i := (HomologicalComplex.shortComplexFunctor C c i).map φ
  change IsIso (F.map (ShortComplex.homologyMap ψ))
  let α : ((K.sc i).map F).homology ⟶ ((L.sc i).map F).homology :=
    ShortComplex.homologyMap (F.mapShortComplex.map ψ)
  have : IsIso α :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map φ) i))
  have hcomp : IsIso (α ≫ ((L.sc i).mapHomologyIso F).hom) := by infer_instance
  have heq : α ≫ ((L.sc i).mapHomologyIso F).hom =
      ((K.sc i).mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap ψ) :=
    ShortComplex.mapHomologyIso_hom_naturality ψ F
  have : IsIso (((K.sc i).mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap ψ)) := heq ▸ hcomp
  exact IsIso.of_isIso_comp_left (((K.sc i).mapHomologyIso F).hom) _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.HomologyIsIso
