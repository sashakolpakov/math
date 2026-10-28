import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mixed.SheafQuasiIsoLocality

/-! # Conservative Exact Family -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConservativeExactFamily.Family

noncomputable section

/-! A family of exact functors which detects zero objects also detects quasi-isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z t

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type t}
  {D : ι → Type w} [∀ i, Category.{z} (D i)] [∀ i, Abelian (D i)]
  (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive]
  [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
  (hzero : ∀ X : C, (∀ i, IsZero ((F i).obj X)) → IsZero X)

include hzero in
theorem isIso {X Y : C} (f : X ⟶ Y) (hf : ∀ i, IsIso ((F i).map f)) : IsIso f := by
  have hk : IsZero (kernel f) := hzero (kernel f) (fun i => by
    let : IsIso ((F i).map f) := hf i
    exact (isZero_kernel_of_mono ((F i).map f)).of_iso (PreservesKernel.iso (F i) f))
  have hc : IsZero (cokernel f) := hzero (cokernel f) (fun i => by
    let : IsIso ((F i).map f) := hf i
    exact (isZero_cokernel_of_epi ((F i).map f)).of_iso (PreservesCokernel.iso (F i) f))
  let : Mono f := Abelian.mono_of_kernel_ι_eq_zero f (hk.eq_of_src _ _)
  let : Epi f := Abelian.epi_of_cokernel_π_eq_zero f (hc.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi f

include hzero in
theorem quasiIso_complex {α : Type*} {c : ComplexShape α} {K L : HomologicalComplex C c} (f : K ⟶ L)
    (hf : ∀ i, QuasiIso (((F i).mapHomologicalComplex c).map f)) : QuasiIso f := by
  constructor
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap f n).mpr
  apply isIso F hzero
  intro i
  let hm : IsIso (HomologicalComplex.homologyMap (((F i).mapHomologicalComplex c).map f) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp ((hf i).quasiIsoAt n)
  let eK := (K.sc n).mapHomologyIso (F i)
  let eL := (L.sc n).mapHomologyIso (F i)
  have h : HomologicalComplex.homologyMap (((F i).mapHomologicalComplex c).map f) n ≫ eL.hom =
      eK.hom ≫ (F i).map (HomologicalComplex.homologyMap f n) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C c n).map f) (F i)
  let : IsIso eK.hom := eK.isIso_hom
  let : IsIso eL.hom := eL.isIso_hom
  have hc : IsIso (HomologicalComplex.homologyMap (((F i).mapHomologicalComplex c).map f) n ≫ eL.hom) :=
    IsIso.comp_isIso' hm eL.isIso_hom
  have hr : IsIso (eK.hom ≫ (F i).map (HomologicalComplex.homologyMap f n)) := h ▸ hc
  exact (isIso_comp_left_iff eK.hom _).mp hr

include hzero in
theorem quasiIso {K L : CochainComplex C ℕ} (f : K ⟶ L)
    (hf : ∀ i, QuasiIso (((F i).mapHomologicalComplex (.up ℕ)).map f)) : QuasiIso f :=
  quasiIso_complex F hzero f hf

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConservativeExactFamily.Family
