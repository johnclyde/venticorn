<!-- Modified for Venticorn: wrapping headings and keyboard-accessible navigation. -->
<script lang="ts">
  export let searchResponse: SearchResponse;
  export let showLocation: (uri: string, range: Range) => void;

  function callback() {
    if (searchResponse.goalRange !== null) {
      showLocation(searchResponse.uri, searchResponse.goalRange);
    }
  }
</script>

{#if searchResponse.goalName === null}
  <h1 class="header">There is no goal.</h1>
{:else if searchResponse.goalRange === null}
  <h1 class="header">{searchResponse.goalName}</h1>
{:else}
  <h1 class="header">
    <button class="goal-link" type="button" on:click={callback}
      >{searchResponse.goalName}</button>
  </h1>
{/if}

<style>
  .goal-link {
    display: block;
    width: 100%;
    border: 0;
    padding: 0;
    background: none;
    color: inherit;
    font: inherit;
    text-align: start;
    overflow-wrap: anywhere;
    cursor: pointer;
  }

  .goal-link:hover,
  .goal-link:focus-visible {
    text-decoration: underline;
  }
</style>
