import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-! # Finite Etale Lift -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleLift.FiniteEtaleLimits

/-!
# TorsionQuotient: finite limits of finite etale schemes over a base

The property-defined slice creates finite limits in the ordinary slice.
Thus finite products and equalizers below retain their all-test-scheme
universal properties, as well as finite etaleness.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w

abbrev property : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

instance : property.{u}.IsMultiplicative where
  id_mem X := ⟨inferInstance, inferInstance⟩
  comp_mem f g hf hg := by
    let : IsFinite f := hf.1
    let : IsFinite g := hg.1
    let : Etale f := hf.2
    let : Etale g := hg.2
    exact ⟨inferInstance, Etale.etale_comp f g⟩

instance : property.{u}.IsStableUnderBaseChange where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback (P := @IsFinite) sq hg.1,
      MorphismProperty.of_isPullback (P := @Etale) sq hg.2⟩

instance : property.{u}.HasOfPostcompProperty property where
  of_postcomp {X Y Z} f g hg hfg := by
    let : IsFinite g := hg.1
    let : Etale g := hg.2
    let : IsFinite (f ≫ g) := hfg.1
    let : Etale (f ≫ g) := hfg.2
    exact ⟨IsFinite.of_comp f g, Etale.of_comp f g⟩

noncomputable def liftDiagram {S : Scheme.{u}} {J : Type v} [Category.{w} J]
    (D : J ⥤ Over S) (hD : ∀ j, property (D.obj j).hom) :
    J ⥤ property.Over ⊤ S :=
  MorphismProperty.Comma.lift D hD (fun _ => trivial) (fun _ => trivial)

theorem finite_limit {S : Scheme.{u}} {J : Type v} [SmallCategory J] [FinCategory J]
    (D : J ⥤ Over S) (hD : ∀ j, property (D.obj j).hom) :
    IsFinite (limit D).hom ∧ Etale (limit D).hom := by
  let : HasFiniteLimits (property.{u}.Over ⊤ S) := inferInstance
  let : PreservesFiniteLimits (MorphismProperty.Over.forget property ⊤ S) := inferInstance
  let F := liftDiagram D hD
  let U := MorphismProperty.Over.forget property ⊤ S
  let e : U.obj (limit F) ≅ limit D := preservesLimitIso U F
  have h : property (U.obj (limit F)).hom := (limit F).prop
  let : IsFinite (U.obj (limit F)).hom := h.1
  let : Etale (U.obj (limit F)).hom := h.2
  let : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget S).mapIso e).inv))
  constructor
  · rw [← e.inv.w]
    infer_instance
  · rw [← e.inv.w]
    infer_instance

theorem product_finite_etale {S : Scheme.{u}} (X : Over S)
    [IsFinite X.hom] [Etale X.hom] (I : Type v) [Finite I] :
    IsFinite (piObj (fun _ : I => X)).hom ∧ Etale (piObj (fun _ : I => X)).hom := by
  let : Fintype I := Fintype.ofFinite I
  exact finite_limit (Discrete.functor (fun _ : I => X))
    (fun _ => show property X.hom from ⟨inferInstance, inferInstance⟩)

theorem equalizer_finite_etale {S : Scheme.{u}} {X Y : Over S}
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom]
    (f g : X ⟶ Y) :
    IsFinite (equalizer f g).hom ∧ Etale (equalizer f g).hom := by
  apply finite_limit (parallelPair f g)
  intro j
  cases j
  · exact show property X.hom from ⟨inferInstance, inferInstance⟩
  · exact show property Y.hom from ⟨inferInstance, inferInstance⟩

theorem hom_finite_etale {S : Scheme.{u}} {X Y : Over S}
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom]
    (f : X ⟶ Y) : IsFinite f.left ∧ Etale f.left := by
  have hfin : IsFinite (f.left ≫ Y.hom) := by simpa only [Over.w] using (inferInstance : IsFinite X.hom)
  have het : Etale (f.left ≫ Y.hom) := by simpa only [Over.w] using (inferInstance : Etale X.hom)
  let : IsFinite (f.left ≫ Y.hom) := hfin
  let : Etale (f.left ≫ Y.hom) := het
  exact ⟨IsFinite.of_comp f.left Y.hom, Etale.of_comp f.left Y.hom⟩

theorem equalizer_open_closed {S : Scheme.{u}} {X Y : Over S}
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom]
    (f g : X ⟶ Y) :
    IsOpenImmersion (equalizer.ι f g).left ∧ IsClosedImmersion (equalizer.ι f g).left := by
  obtain ⟨hfin, het⟩ := equalizer_finite_etale f g
  let : IsFinite (equalizer f g).hom := hfin
  let : Etale (equalizer f g).hom := het
  obtain ⟨hιfin, hιet⟩ := hom_finite_etale (equalizer.ι f g)
  let : IsFinite (equalizer.ι f g).left := hιfin
  let : Etale (equalizer.ι f g).left := hιet
  refine ⟨IsOpenImmersion.of_flat_of_mono _, ?_⟩
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleLift.FiniteEtaleLimits
