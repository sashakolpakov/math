import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorCoefficientChange

/-! # Section Tensor Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.SectionTensorValues

noncomputable section

/-! Two successive section tensor comparisons agree on pure tensors with the comparison for the composite pullback. The scalar factors multiply through the given algebra map, and the target is identified by the actual pullback-composition isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

theorem moduleSectionTensorComparisonApp_mul_tmul
    {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f)
    (U : X.Opens) (b c : B) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (op U)) :
    (show Γ((Scheme.Modules.pullback a).obj M, a ⁻¹ᵁ U) from
      Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U ((b * c) ⊗ₜ[R] x)) =
      Y.presheaf.map (a ⁻¹ᵁ U).leTop.op (q b) •
        (show Γ((Scheme.Modules.pullback a).obj M, a ⁻¹ᵁ U) from
          Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U (c ⊗ₜ[R] x)) := by
  let v : Γ((Scheme.Modules.pullback a).obj M, a ⁻¹ᵁ U) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app U x
  change Y.presheaf.map (a ⁻¹ᵁ U).leTop.op (q (b * c)) • v =
    Y.presheaf.map (a ⁻¹ᵁ U).leTop.op (q b) • (Y.presheaf.map (a ⁻¹ᵁ U).leTop.op (q c) • v)
  rw [map_mul, map_mul, mul_smul]

theorem sectionTensor_composite_coefficients
    {X Y Z : Scheme.{u}} {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    (a : X ⟶ Y) (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (r : C →+* Γ(X, ⊤))
    (hr : r.comp (algebraMap R C) = (a ≫ g).appTop.hom.comp f) :
    r.comp (algebraMap R C) = a.appTop.hom.comp (g.appTop.hom.comp f) := by
  ext z
  exact DFunLike.congr_fun hr z

theorem moduleSectionTensorComparisonApp_iterated_tmul
    {X Y Z : Scheme.{u}} {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C]
    (a : X ⟶ Y) (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (M : Z.Modules)
    (q : B →+* Γ(Y, ⊤)) (r : C →+* Γ(X, ⊤))
    (hq : q.comp (algebraMap R B) = g.appTop.hom.comp f)
    (hr : r.comp (algebraMap R C) = (a ≫ g).appTop.hom.comp f)
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = a.appTop.hom.comp q)
    (U : Z.Opens) (b : B) (c : C) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (op U)) :
    ((Scheme.Modules.pullbackComp a g).hom.app M).app ((a ≫ g) ⁻¹ᵁ U)
      (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (g.appTop.hom.comp f) ((Scheme.Modules.pullback g).obj M)
        r (sectionTensor_composite_coefficients a g f r hr) (g ⁻¹ᵁ U)
          (c ⊗ₜ[R] (show (Coefficient.ModulePresheaf.coefficientModulePresheaf (g.appTop.hom.comp f)
              ((Scheme.Modules.pullback g).obj M)).obj (op (g ⁻¹ᵁ U)) from
            Module.SectionTensorComparison.moduleSectionTensorComparisonApp g f M q hq U (b ⊗ₜ[R] x)))) =
      Module.SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ g) f M r hr U ((c * α b) ⊗ₜ[R] x) := by
  let V := g ⁻¹ᵁ U
  let W := (a ≫ g) ⁻¹ᵁ U
  let N : Y.Modules := (Scheme.Modules.pullback g).obj M
  let K : X.Modules := (Scheme.Modules.pullback a).obj N
  let L : X.Modules := (Scheme.Modules.pullback (a ≫ g)).obj M
  let e : K ⟶ L := (Scheme.Modules.pullbackComp a g).hom.app M
  let z : (Coefficient.ModulePresheaf.coefficientModulePresheaf (g.appTop.hom.comp f) N).obj (op V) :=
    Module.SectionTensorComparison.moduleSectionTensorComparisonApp g f M q hq U (b ⊗ₜ[R] x)
  let u : Γ(K, W) := ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app N).app V z
  let d : Γ(X, W) := X.presheaf.map W.leTop.op (r c)
  have ho : (show Γ(K, W) from
      Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (g.appTop.hom.comp f) N r
        (sectionTensor_composite_coefficients a g f r hr) V (c ⊗ₜ[R] z)) = d • u :=
    Module.TensorSectionValues.moduleSectionTensorComparisonApp_value a (g.appTop.hom.comp f) N r
      (sectionTensor_composite_coefficients a g f r hr) V c z
  have he : e.app W u = Module.SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ g) f M r hr U (α b ⊗ₜ[R] x) :=
    Module.TensorCoefficientChange.moduleSectionTensorComparisonApp_refine_coefficient_change a g f M q r hq hr α hα U b x
  have hm := moduleSectionTensorComparisonApp_mul_tmul (a ≫ g) f M r hr U c (α b) x
  exact (congrArg (e.app W) ho).trans ((e.app_smul d u).trans
    ((congrArg (fun v : Γ(L, W) => d • v) he).trans hm.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.SectionTensorValues
