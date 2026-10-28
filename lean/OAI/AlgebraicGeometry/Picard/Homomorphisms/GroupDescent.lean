import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup

/-! # Group Descent -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupDescent

noncomputable section

/-! Descent of actual group morphisms through the Frobenius quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {A B C : Over S}

theorem overRelations_left (f : A ⟶ B) (g : A ⟶ C)
    (hg : ∀ {T : Over S} (x y : T ⟶ A), x ≫ f = y ≫ f → x ≫ g = y ≫ g) :
    ∀ {T : Scheme.{u}} (x y : T ⟶ A.left),
      x ≫ f.left = y ≫ f.left → x ≫ g.left = y ≫ g.left := by
  intro T x y hxy
  let T' : Over S := Over.mk (x ≫ A.hom)
  let x' : T' ⟶ A := Over.homMk x rfl
  let y' : T' ⟶ A := Over.homMk y (by
    change y ≫ A.hom = x ≫ A.hom
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, hxy])
  exact congrArg Over.Hom.left (hg x' y' (Over.OverMorphism.ext hxy))

/-- The fpqc effective epimorphism property also holds in the slice. -/
theorem effectiveEpi_over_of_fpqc (f : A ⟶ B)
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left] : EffectiveEpi f := by
  constructor
  refine ⟨{ desc := ?_, fac := ?_, uniq := ?_ }⟩
  · intro W g hg
    let d := EffectiveEpi.desc f.left g.left (overRelations_left f g hg)
    refine Over.homMk d ?_
    apply (cancel_epi f.left).mp
    rw [← Category.assoc, EffectiveEpi.fac, Over.w g, Over.w f]
  · intro W g hg
    apply Over.OverMorphism.ext
    exact EffectiveEpi.fac f.left g.left (overRelations_left f g hg)
  · intro W g hg m hm
    apply Over.OverMorphism.ext
    exact EffectiveEpi.uniq f.left g.left (overRelations_left f g hg)
      m.left (congrArg Over.Hom.left hm)

variable [GrpObj A] [GrpObj B] [GrpObj C]

theorem exists_unique_descent_of_kernel (f : A ⟶ B) [IsMonHom f]
    [EffectiveEpi f] (g : A ⟶ C) [IsMonHom g]
    (hg : Kernel.Construction.kernelInclusion f ≫ g = 1) : ∃! d : B ⟶ C, f ≫ d = g := by
  have hrel : ∀ {T : Over S} (x y : T ⟶ A),
      x ≫ f = y ≫ f → x ≫ g = y ≫ g := by
    intro T x y hxy
    have hker : (x / y) ≫ f = 1 := by
      rw [GrpObj.div_comp, hxy, div_self']
    obtain ⟨k, hk, _⟩ := (Kernel.Construction.kernelScheme_universal f T (x / y)).mp hker
    have h : (x / y) ≫ g = 1 := by
      rw [← hk, Category.assoc, hg, MonObj.comp_one]
    rwa [GrpObj.div_comp, div_eq_one] at h
  exact ⟨EffectiveEpi.desc f g hrel, EffectiveEpi.fac f g hrel,
    fun d hd => EffectiveEpi.uniq f g hrel d hd⟩

theorem descended_isMonHom (f : A ⟶ B) [IsMonHom f] [Epi (f ⊗ₘ f)]
    (g : A ⟶ C) [IsMonHom g] (d : B ⟶ C) (hd : f ≫ d = g) : IsMonHom d := by
  constructor
  · rw [← IsMonHom.one_hom f, Category.assoc, hd, IsMonHom.one_hom g]
  · apply (cancel_epi (f ⊗ₘ f)).mp
    rw [← Category.assoc, ← IsMonHom.mul_hom f, Category.assoc, hd,
      IsMonHom.mul_hom g]
    rw [← Category.assoc, tensorHom_comp_tensorHom, hd]

theorem groupHom_pow_isMonHom [IsCommMonObj C]
    (g : A ⟶ C) [IsMonHom g] (n : ℕ) : IsMonHom (g ^ n) := by
  induction n with
  | zero =>
      change IsMonHom (toUnit A ≫ η[C])
      infer_instance
  | succ n ih =>
      have : IsMonHom (g ^ n) := ih
      rw [pow_succ, Hom.mul_def]
      infer_instance

omit [GrpObj A] [GrpObj B] in
theorem effectiveEpi_tensor_over_of_fpqc {X Y : Over S}
    (f : A ⟶ B) (g : X ⟶ Y)
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    [Flat g.left] [Surjective g.left] [QuasiCompact g.left] :
    EffectiveEpi (f ⊗ₘ g) := by
  let : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.Surjective.{u}) :=
    ⟨fun _ _ hf hg => ⟨hg.1.comp hf.1⟩⟩
  have hprop (P : MorphismProperty Scheme.{u})
      [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
      (hf : P f.left) (hg : P g.left) : P (f ⊗ₘ g).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap hf hg (Over.w f).symm (Over.w g).symm
  have : Flat (f ⊗ₘ g).left := hprop (@Flat) inferInstance inferInstance
  have : Surjective (f ⊗ₘ g).left :=
    hprop (@AlgebraicGeometry.Surjective) inferInstance inferInstance
  have : QuasiCompact (f ⊗ₘ g).left := hprop (@QuasiCompact) inferInstance inferInstance
  exact effectiveEpi_over_of_fpqc (f ⊗ₘ g)

theorem exists_unique_groupDescent_of_fpqc (f : A ⟶ B) [IsMonHom f]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (g : A ⟶ C) [IsMonHom g] (hg : Kernel.Construction.kernelInclusion f ≫ g = 1) :
    ∃! d : B ⟶ C, IsMonHom d ∧ f ≫ d = g := by
  have : EffectiveEpi f := effectiveEpi_over_of_fpqc f
  have : EffectiveEpi (f ⊗ₘ f) := effectiveEpi_tensor_over_of_fpqc f f
  obtain ⟨d, hd, hu⟩ := exists_unique_descent_of_kernel f g hg
  exact ⟨d, ⟨descended_isMonHom f g d hd, hd⟩, fun e he => hu e he.2⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupDescent
