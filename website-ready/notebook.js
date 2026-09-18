const filters = document.querySelector('.filters');
const buttons = [...document.querySelectorAll('[data-filter]')];
const papers = [...document.querySelectorAll('.paper')];
function selectTopic(topic) {
  let visible = 0;
  papers.forEach(paper => {
    paper.hidden = topic !== 'all' && !paper.dataset.tags.split(' ').includes(topic);
    if (!paper.hidden) visible++;
  });
  buttons.forEach(button => button.setAttribute('aria-pressed', String(button.dataset.filter === topic)));
  document.querySelector('#result-count').textContent = `${visible} of ${papers.length} selected works`;
}
if (filters) {
filters.hidden = false;
buttons.forEach(button => button.addEventListener('click', () => selectTopic(button.dataset.filter)));
document.querySelectorAll('[data-topic]').forEach(link => link.addEventListener('click', () => selectTopic(link.dataset.topic)));
const initial = new URLSearchParams(location.search).get('topic');
selectTopic(buttons.some(b => b.dataset.filter === initial) ? initial : 'all');
}
