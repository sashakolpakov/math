import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedRecovery

/-! # Kernel Scalar Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelScalarRecovery

noncomputable section

/-!
# CartierDuality: character evaluation recovered from the actual descended line
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters
section

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- The difference between a point and its kernel translate is exactly that kernel element. -/
theorem kernelDifference_translate {T : Over S} (x : T ⟶ A) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x (x * (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)) (Picard.Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f x z).symm = z := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion]
  exact inv_mul_cancel_left x (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)

variable (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

include hχ in
/-- The native test-scheme formula agrees with evaluation in the original category over the base. -/
theorem differenceScalar_native {T : Over S} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ (x ≫ f).left x.left y.left rfl (congrArg Over.Hom.left h.symm) =
      (χ T (KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x y h)).val := by
  let U := Over.mk ((x ≫ f).left ≫ B.hom)
  let t : T ⟶ U := Over.homMk (𝟙 T.left) ((Category.id_comp _).trans (Over.w (x ≫ f)))
  let px := KernelCharacterGluing.Construction.KernelCharacters.coverPoint f (x ≫ f).left x.left rfl
  let py := KernelCharacterGluing.Construction.KernelCharacters.coverPoint f (x ≫ f).left y.left (congrArg Over.Hom.left h.symm)
  have hpx : t ≫ px = x := Over.OverMorphism.ext (Category.id_comp _)
  have hpy : t ≫ py = y := Over.OverMorphism.ext (Category.id_comp _)
  have hd : px ≫ f = py ≫ f :=
    (KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f _ _ rfl).trans (KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f _ _ (congrArg Over.Hom.left h.symm)).symm
  let z := KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f px py hd
  have hz : t ≫ z = KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x y h :=
    (KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_natural f t px py hd).trans
      (KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_congr f _ _ x y _ h hpx hpy)
  have hn := congrArg Units.val (hχ t z)
  change t.left.appTop (χ U z).val = (χ T (t ≫ z)).val at hn
  rw [show t.left = 𝟙 T.left from rfl, Scheme.Hom.id_appTop] at hn
  exact hn.trans (congrArg (fun a => (χ T a).val) hz)

include hχ in
/-- Character gluing on a kernel translate is the actual character value. -/
theorem differenceScalar_translate {T : Over S} (x : T ⟶ A) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ (x ≫ f).left x.left (x * (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).left rfl
      (congrArg Over.Hom.left (Picard.Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f x z)) = (χ T z).val :=
  (differenceScalar_native f χ hχ x (x * (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f))
    (Picard.Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f x z).symm).trans
    (congrArg (fun a => (χ T a).val) (kernelDifference_translate f x z))

variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (he : ∀ {T : Scheme.{u}} (q : T ⟶ B.left) (x y : T ⟶ A.left)
      (hx : x ≫ f.left = q) (hy : y ≫ f.left = q),
      DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf)
        (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ) e.hom q x y hx hy)

include he in
/-- Every recovered line has the supplied character on every kernel-valued test point. -/
theorem recoveredLine_kernelValue {T : Over S} (x : T ⟶ A) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalar f (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf) e x z = (χ T z).val :=
  (FramedRecovery.Construction.LineDescent.scalarCocycle_recovery (KernelCharacterGluing.Construction.KernelCharacters.characterScalarCocycle f χ hχ) L e
    (x ≫ f).left x.left (x * (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).left rfl
    (congrArg Over.Hom.left (Picard.Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f x z))
    (he _ _ _ _ _)).trans (differenceScalar_translate f χ hχ x z)

include he in
/-- The universal kernel scalar of the recovered line is the original regular character. -/
theorem recoveredLine_kernelScalar :
    (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L e).kernelScalar = (χ (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) (𝟙 (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).val :=
  recoveredLine_kernelValue f χ hχ L e he 1 (𝟙 (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))

end

variable {R C : Type u} [CommRing R] [CommRing C] [HopfAlgebra R C]
    {A B : Over (Spec (.of R))} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (i : Characters.Construction.affineHopfGroupScheme R C ≅ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) (z : GroupLike R C)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (he : ∀ {T : Scheme.{u}} (q : T ⟶ B.left) (x y : T ⟶ A.left)
      (hx : x ≫ f.left = q) (hy : y ≫ f.left = q),
      DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf)
        (KernelCharacterGluing.Construction.KernelCharacters.hopfCharacterLineDatum f i z) e.hom q x y hx hy)

include he in
/-- The actual Hopf coordinate recovered from the descended line is the original group-like element. -/
theorem recoveredLine_hopfCoordinate :
    (Scheme.ΓSpecIso (.of C)).hom
      (i.hom.hom.hom.left.appTop (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L e).kernelScalar) = z.val := by
  have hs := recoveredLine_kernelScalar f (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom f i z)
    (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom_natural f i z) L e he
  have hv : (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom f i z (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) (𝟙 (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).val =
      i.inv.hom.hom.left.appTop (HopfScalarsOf.Construction.HopfScalars.coordinateSection C z.val) := by
    change (𝟙 (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) ≫ i.inv.hom.hom).left.appTop _ = _
    rw [Category.id_comp]
  have hi : i.hom.hom.hom.left ≫ i.inv.hom.hom.left = 𝟙 (Spec (.of C)) :=
    congrArg (fun a => a.hom.hom.left) i.hom_inv_id
  have hc : i.hom.hom.hom.left.appTop
      (i.inv.hom.hom.left.appTop (HopfScalarsOf.Construction.HopfScalars.coordinateSection C z.val)) =
        HopfScalarsOf.Construction.HopfScalars.coordinateSection C z.val :=
    congrArg (fun a : Spec (.of C) ⟶ Spec (.of C) => a.appTop (HopfScalarsOf.Construction.HopfScalars.coordinateSection C z.val)) hi
  exact (congrArg (fun s => (Scheme.ΓSpecIso (.of C)).hom (i.hom.hom.hom.left.appTop s))
    (hs.trans hv)).trans ((congrArg (Scheme.ΓSpecIso (.of C)).hom hc).trans
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of C)).inv_hom_id z.val))

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelScalarRecovery
