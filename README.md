# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/rocket-48.png) Pluto
A web server written in Coq.

## Run with OPAM
Add the Coq repositories:

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam repo add coq-testing https://github.com/coq/repo-testing.git
    opam repo add coq-unstable https://github.com/coq/repo-unstable.git

Install Pluto:

    opam install coq:concurrency:pluto

Run it on some `html/` folder:

    pluto.native 8000 html/

Your website is now available on [localhost:8000](http://localhost:8000/).

## Run with Docker
Add some HTML content to `html/`, build and run the server:

    docker build --tag=pluto .
    docker run -ti -p 80:80 pluto

Your website is now available on [localhost](http://localhost/).
