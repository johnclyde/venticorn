<!-- Modified for Venticorn: keyboard-accessible source navigation. -->
<script lang="ts">
  export let step: ProofStepInfo;
  export let showLocation: (uri: string, range: Range) => void;
</script>

{#if step.location !== null}
  from <button
    type="button"
    class="preview-link"
    on:click={() => {
      if (step.location !== null) {
        showLocation(step.location.uri, step.location.range);
      }
    }}>{step.rule}</button
  >
{:else}
  by <span>{step.rule}</span>
{/if}

<style>
  .preview-link {
    border: 0;
    padding: 0;
    background: none;
    font: inherit;
    cursor: pointer;
    color: var(--vscode-textLink-foreground);
  }

  .preview-link:hover,
  .preview-link:focus-visible {
    text-decoration: underline;
  }
</style>
