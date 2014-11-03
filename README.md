# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/rocket-48.png) Web Server
A web server written in Coq.

## Usage
Add some HTML content to `html/`, build and run the server:

    docker build --tag=web-server .
    docker run -ti -p 80:80 web-server

Your website should be available on [localhost](http://localhost/).