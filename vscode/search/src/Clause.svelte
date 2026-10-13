<!-- Modified for Venticorn: CSS indentation and keyboard-accessible clause navigation. -->
<script lang="ts">
  export let clause: ClauseInfo;
  export let onClick: null | ((id: number) => void) = null;
</script>

{#if clause.id !== null && onClick !== null}
  <button
    class="indent clause-link"
    type="button"
    on:click={() => {
      if (clause.id !== null && onClick !== null) {
        onClick(clause.id);
      }
    }}>{clause.text}</button
  >
{:else}
  <span class="indent">{clause.text}</span>
{/if}

<style>
  .clause-link {
    width: 100%;
    box-sizing: border-box;
    border: 0;
    padding-block: 0;
    padding-inline-end: 0;
    background: none;
    color: inherit;
    font-size: inherit;
    line-height: inherit;
    text-align: start;
    cursor: pointer;
  }

  .clause-link:hover,
  .clause-link:focus-visible {
    text-decoration: underline;
  }
</style>
