/* Expand Part I and Part II in the sidebar on the book landing page. */
document.addEventListener("DOMContentLoaded", function () {
  const path = window.location.pathname;
  const onBookLanding =
    /\/book\/index\.html$/i.test(path) || /\/book\/?$/i.test(path);
  if (!onBookLanding) {
    return;
  }
  const tree = document.querySelector(".sidebar-scroll .sidebar-tree");
  if (!tree) {
    return;
  }
  tree
    .querySelectorAll('a[href$="part-i/index.html"], a[href$="part-ii/index.html"]')
    .forEach(function (link) {
      const item = link.closest("li.has-children");
      const toggle = item && item.querySelector("input.toctree-checkbox");
      if (toggle) {
        toggle.checked = true;
      }
    });
});